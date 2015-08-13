use std::iter::IntoIterator;
use std::io;
use std::u8;
use std::u16;
use std::u32;

use byteorder::{ByteOrder, BigEndian};
use serde::{self, Serialize};

use {CborError, CborResult, Type, WriteError};

/// Serializes Rust values to CBOR bytes in the underlying writer `W`.
///
/// Note that currently, using the serialization infrastructure is the only
/// way to write CBOR in this crate.
pub struct Serializer<W> {
    buf: W,
    emitting_key: bool,
    byte_string: bool,
    tag: bool,
    skip_key: bool,
}

impl<W: io::Write> Serializer<W> {
    fn write_num(&mut self, major: u8, n: u64) -> CborResult<()> {
        let major = major << 5;
        if n <= 23 {
            fromerr!(self.buf.write_all(&[major | n as u8]))
        } else if n <= u8::MAX as u64 {
            fromerr!(self.buf.write_all(&[major | 24, n as u8]))
        } else if n <= u16::MAX as u64 {
            let mut buf = [major | 25, 0, 0];
            <BigEndian as ByteOrder>::write_u16(&mut buf[1..], n as u16);
            fromerr!(self.buf.write_all(&buf))
        } else if n <= u32::MAX as u64 {
            let mut buf = [major | 26, 0, 0, 0, 0];
            <BigEndian as ByteOrder>::write_u32(&mut buf[1..], n as u32);
            fromerr!(self.buf.write_all(&buf))
        } else {
            let mut buf = [major | 27, 0, 0, 0, 0, 0, 0, 0, 0];
            <BigEndian as ByteOrder>::write_u64(&mut buf[1..], n);
            fromerr!(self.buf.write_all(&buf))
        }
    }

    fn write_uint(&mut self, n: u64) -> CborResult<()> {
        self.write_num(0, n)
    }

    fn write_int(&mut self, n: i64) -> CborResult<()> {
        if n >= 0 {
            self.write_uint(n as u64)
        } else {
            self.write_num(1, (-1 - n) as u64)
        }
    }
}

impl<W: io::Write> Serializer<W> {
    /// Serialize CBOR to an arbitrary writer.
    pub fn from_writer(wtr: W) -> Serializer<io::BufWriter<W>> {
        Serializer::from_writer_raw(io::BufWriter::new(wtr))
    }

    fn from_writer_raw(wtr: W) -> Serializer<W> {
        Serializer {
            buf: wtr,
            emitting_key: false,
            byte_string: false,
            tag: false,
            skip_key: false,
        }
    }

    /// Serialize an iterator of Rust values to CBOR in the underlying writer.
    ///
    /// Every value in the iterator must satisfy `Serialize` (from the
    /// `serde` crate).
    ///
    /// Note that this serializes top-level CBOR data items. They can be decoded
    /// in a streaming fashion.
    ///
    /// # Example
    ///
    /// Serialize a list of numbers.
    ///
    /// ```rust
    /// use cbor::Serializer;
    ///
    /// let mut ser = Serializer::from_memory();
    /// ser.serialize(&[1, 2, 3, 4, 5]);
    /// assert_eq!(vec![1, 2, 3, 4, 5], ser.as_bytes());
    /// ```
    pub fn serialize<I, T>(&mut self, it: I) -> CborResult<()>
        where I: IntoIterator<Item=T>,
              T: Serialize {
        for v in it {
            try!(v.serialize(self));
        }
        Ok(())
    }

    /// Flush the underlying writer.
    pub fn flush(&mut self) -> CborResult<()> {
        fromerr!(self.buf.flush())
    }
}

impl Serializer<Vec<u8>> {
    /// Serialize CBOR to an in memory buffer.
    pub fn from_memory() -> Serializer<Vec<u8>> {
        Serializer::from_writer_raw(Vec::with_capacity(1024 * 64))
    }

    /// Flush and retrieve the CBOR bytes that have been written.
    pub fn as_bytes(&mut self) -> &[u8] {
        self.flush().unwrap();
        &self.buf
    }

    /// Flush and retrieve the CBOR bytes that have been written without
    /// copying.
    pub fn into_bytes(mut self) -> Vec<u8> {
        self.flush().unwrap();
        self.buf
    }
}

// /// Encodes a data item directly to CBOR bytes.
// ///
// /// This is useful when writing `Encodable` implementations with
// /// `CborTagEncode`.
// pub fn encode<E: Encodable>(v: E) -> CborResult<Vec<u8>> {
    // let mut enc = Encoder::from_memory();
    // try!(enc.encode(&[v]));
    // Ok(enc.into_bytes())
// }

macro_rules! no_string_key {
    ($enc:expr) => (
        if $enc.emitting_key {
            return Err(CborError::Encode(WriteError::InvalidMapKey {
                got: None,
            }));
        }
    );
    ($enc:expr, $ty:expr) => (
        if $enc.emitting_key {
            return Err(CborError::Encode(WriteError::InvalidMapKey {
                got: Some($ty),
            }));
        }
    );
}

impl<W: io::Write> serde::Serializer for Serializer<W> {
    type Error = CborError;

    fn visit_unit(&mut self) -> CborResult<()> {
        no_string_key!(self, Type::Null);
        fromerr!(self.buf.write_all(&[(7 << 5) | 22]))
    }

    fn visit_usize(&mut self, v: usize) -> CborResult<()> {
        no_string_key!(self, Type::UInt);
        self.write_uint(v as u64)
    }

    fn visit_u64(&mut self, v: u64) -> CborResult<()> {
        no_string_key!(self, Type::UInt64);
        if self.tag {
            self.write_num(6, v)
        } else {
            self.write_uint(v)
        }
    }

    fn visit_u32(&mut self, v: u32) -> CborResult<()> {
        no_string_key!(self, Type::UInt32);
        self.write_uint(v as u64)
    }

    fn visit_u16(&mut self, v: u16) -> CborResult<()> {
        no_string_key!(self, Type::UInt16);
        self.write_uint(v as u64)
    }

    fn visit_u8(&mut self, v: u8) -> CborResult<()> {
        no_string_key!(self, Type::UInt8);
        if self.byte_string {
            fromerr!(self.buf.write_all(&[v]))
        } else {
            self.write_uint(v as u64)
        }
    }

    fn visit_isize(&mut self, v: isize) -> CborResult<()> {
        no_string_key!(self, Type::Int);
        self.write_int(v as i64)
    }

    fn visit_i64(&mut self, v: i64) -> CborResult<()> {
        no_string_key!(self, Type::Int64);
        self.write_int(v)
    }

    fn visit_i32(&mut self, v: i32) -> CborResult<()> {
        no_string_key!(self, Type::Int32);
        self.write_int(v as i64)
    }

    fn visit_i16(&mut self, v: i16) -> CborResult<()> {
        no_string_key!(self, Type::Int16);
        self.write_int(v as i64)
    }

    fn visit_i8(&mut self, v: i8) -> CborResult<()> {
        no_string_key!(self, Type::Int8);
        self.write_int(v as i64)
    }

    fn visit_f64(&mut self, v: f64) -> CborResult<()> {
        no_string_key!(self, Type::Float64);
        let mut buf = [(7 << 5) | 27, 0, 0, 0, 0, 0, 0, 0, 0];
        <BigEndian as ByteOrder>::write_f64(&mut buf[1..], v);
        fromerr!(self.buf.write_all(&buf))
    }

    fn visit_f32(&mut self, v: f32) -> CborResult<()> {
        no_string_key!(self, Type::Float32);
        let mut buf = [(7 << 5) | 26, 0, 0, 0, 0];
        <BigEndian as ByteOrder>::write_f32(&mut buf[1..], v);
        fromerr!(self.buf.write_all(&buf))
    }

    fn visit_bool(&mut self, v: bool) -> CborResult<()> {
        no_string_key!(self, Type::Bool);
        let n = if v { 21 } else { 20 };
        fromerr!(self.buf.write_all(&[(7 << 5) | n]))
    }

    fn visit_char(&mut self, v: char) -> CborResult<()> {
        no_string_key!(self, Type::UInt32);
        self.visit_u32(v as u32)
    }

    fn visit_str(&mut self, v: &str) -> CborResult<()> {
        try!(self.write_num(3, v.len() as u64));
        fromerr!(self.buf.write_all(v.as_bytes()))
    }

    fn visit_none(&mut self) -> CborResult<()> {
        no_string_key!(self);
        self.visit_unit()
    }

    fn visit_some<T>(&mut self, value: T) -> CborResult<()>
        where T: Serialize,
    {
        no_string_key!(self);
        value.serialize(self)
    }

    fn visit_unit_variant(&mut self,
                          _name: &str,
                          _variant_index: usize,
                          variant: &str) -> CborResult<()> {
        self.visit_str(variant)
    }

    fn visit_seq<V>(&mut self, mut visitor: V) -> CborResult<()>
        where V: serde::ser::SeqVisitor,
    {
        no_string_key!(self, Type::Array);

        let len = visitor.len().unwrap();

        if self.byte_string {
            try!(self.write_num(2, len as u64));
        } else {
            try!(self.write_num(4, len as u64));
        }

        while let Some(()) = try!(visitor.visit(self)) { }

        self.byte_string = false;

        Ok(())
    }

    fn visit_tuple_struct<V>(&mut self,
                             name: &str,
                             mut visitor: V) -> CborResult<()>
        where V: serde::ser::SeqVisitor,
    {
        no_string_key!(self, Type::Map);

        let len = visitor.len().unwrap();

        match name {
            "CborBytes" => {
                self.byte_string = true;
            }
            _ => {
                try!(self.write_num(4, len as u64)); }
        }

        while let Some(()) = try!(visitor.visit(self)) { }

        Ok(())
    }

    fn visit_tuple_variant<V>(&mut self,
                              _name: &str,
                              _variant_index: usize,
                              variant: &str,
                              mut visitor: V) -> CborResult<()>
        where V: serde::ser::SeqVisitor,
    {
        no_string_key!(self);

        try!(self.write_num(5, 1));
        try!(self.visit_str(variant));

        let len = visitor.len().unwrap();
        try!(self.write_num(4, len as u64));

        while let Some(()) = try!(visitor.visit(self)) { }

        Ok(())
    }

    fn visit_seq_elt<T>(&mut self, value: T) -> CborResult<()>
        where T: serde::ser::Serialize,
    {
        no_string_key!(self);
        value.serialize(self)
    }

    fn visit_map<V>(&mut self, mut visitor: V) -> CborResult<()>
        where V: serde::ser::MapVisitor,
    {
        no_string_key!(self, Type::Map);
        let len = visitor.len().unwrap();
        try!(self.write_num(5, len as u64));

        while let Some(()) = try!(visitor.visit(self)) { }

        Ok(())
    }

    fn visit_struct<V>(&mut self, name: &str, mut visitor: V) -> CborResult<()>
        where V: serde::ser::MapVisitor,
    {
        no_string_key!(self, Type::Map);

        match name {
            "CborTag" | "CborTagEncode" => {
                self.tag = true;
            }
            _ => {
                let len = visitor.len().unwrap();
                try!(self.write_num(5, len as u64));
            }
        }

        while let Some(()) = try!(visitor.visit(self)) { }

        Ok(())
    }

    fn visit_struct_variant<V>(&mut self,
                               _name: &str,
                               _variant_index: usize,
                               variant: &str,
                               mut visitor: V) -> CborResult<()>
        where V: serde::ser::MapVisitor,
    {
        no_string_key!(self);

        try!(self.write_num(5, 1));
        try!(self.visit_str(variant));

        let len = visitor.len().unwrap();
        try!(self.write_num(4, len as u64));

        self.skip_key = true;

        while let Some(()) = try!(visitor.visit(self)) { }

        self.skip_key = false;

        Ok(())
    }

    fn visit_map_elt<K, V>(&mut self, key: K, value: V) -> CborResult<()>
        where K: serde::Serialize,
              V: serde::Serialize,
    {
        no_string_key!(self);

        if !self.tag && !self.skip_key {
            self.emitting_key = true;
            try!(key.serialize(self));
            self.emitting_key = false;
        }

        no_string_key!(self);
        value.serialize(self)
    }
}
