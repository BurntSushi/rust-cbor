use std::iter::IntoIterator;
use std::io;
use std::u8;
use std::u16;
use std::u32;

use byteorder::{ByteOrder, BigEndian};
use rustc_serialize::Encodable;
use rustc_serialize::Encoder as RustcEncoder;

use {CborError, CborResult, Type, WriteError};

/// Encodes Rust values to CBOR bytes in the underlying writer `W`.
///
/// Note that currently, using the serialization infrastructure is the only
/// way to write CBOR in this crate.
pub struct Encoder<W> {
    buf: W,
    emitting_key: bool,
    byte_string: bool,
    tag: bool,
}

impl<W: io::Write> Encoder<W> {
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

    fn is_tag_field(&self, name: &str) -> bool {
        self.tag && name.starts_with("__cbor_tag_encode")
    }
}

impl<W: io::Write> Encoder<W> {
    /// Encode CBOR to an arbitrary writer.
    pub fn from_writer(wtr: W) -> Encoder<io::BufWriter<W>> {
        Encoder::from_writer_raw(io::BufWriter::new(wtr))
    }

    fn from_writer_raw(wtr: W) -> Encoder<W> {
        Encoder {
            buf: wtr,
            emitting_key: false,
            byte_string: false,
            tag: false,
        }
    }

    /// Encode an iterator of Rust values to CBOR in the underlying writer.
    ///
    /// Every value in the iterator must satisfy `Encodable` (from the
    /// `rustc-serialize` crate).
    ///
    /// Note that this encodes top-level CBOR data items. They can be decoded
    /// in a streaming fashion.
    ///
    /// # Example
    ///
    /// Encode a list of numbers.
    ///
    /// ```rust
    /// use cbor::Encoder;
    ///
    /// let mut enc = Encoder::from_memory();
    /// enc.encode(&[1, 2, 3, 4, 5]);
    /// assert_eq!(vec![1, 2, 3, 4, 5], enc.as_bytes());
    /// ```
    pub fn encode<I>(&mut self, it: I) -> CborResult<()>
        where I: IntoIterator,
              <<I as IntoIterator>::IntoIter as Iterator>::Item: Encodable {
        for v in it.into_iter() {
            try!(v.encode(self))
        }
        Ok(())
    }

    /// Flush the underlying writer.
    pub fn flush(&mut self) -> CborResult<()> {
        fromerr!(self.buf.flush())
    }
}

impl Encoder<Vec<u8>> {
    /// Encode CBOR to an in memory buffer.
    pub fn from_memory() -> Encoder<Vec<u8>> {
        Encoder::from_writer_raw(Vec::with_capacity(1024 * 64))
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

impl<W: io::Write> RustcEncoder for Encoder<W> {
    type Error = CborError;

    fn emit_nil(&mut self) -> CborResult<()> {
        no_string_key!(self, Type::Null);
        fromerr!(self.buf.write_all(&[(7 << 5) | 22]))
    }

    fn emit_usize(&mut self, v: usize) -> CborResult<()> {
        no_string_key!(self, Type::UInt);
        self.write_uint(v as u64)
    }

    fn emit_u64(&mut self, v: u64) -> CborResult<()> {
        no_string_key!(self, Type::UInt64);
        if self.tag {
            self.write_num(6, v)
        } else {
            self.write_uint(v)
        }
    }

    fn emit_u32(&mut self, v: u32) -> CborResult<()> {
        no_string_key!(self, Type::UInt32);
        self.write_uint(v as u64)
    }

    fn emit_u16(&mut self, v: u16) -> CborResult<()> {
        no_string_key!(self, Type::UInt16);
        self.write_uint(v as u64)
    }

    fn emit_u8(&mut self, v: u8) -> CborResult<()> {
        no_string_key!(self, Type::UInt8);
        if self.byte_string {
            fromerr!(self.buf.write_all(&[v]))
        } else {
            self.write_uint(v as u64)
        }
    }

    fn emit_isize(&mut self, v: isize) -> CborResult<()> {
        no_string_key!(self, Type::Int);
        self.write_int(v as i64)
    }

    fn emit_i64(&mut self, v: i64) -> CborResult<()> {
        no_string_key!(self, Type::Int64);
        self.write_int(v)
    }

    fn emit_i32(&mut self, v: i32) -> CborResult<()> {
        no_string_key!(self, Type::Int32);
        self.write_int(v as i64)
    }

    fn emit_i16(&mut self, v: i16) -> CborResult<()> {
        no_string_key!(self, Type::Int16);
        self.write_int(v as i64)
    }

    fn emit_i8(&mut self, v: i8) -> CborResult<()> {
        no_string_key!(self, Type::Int8);
        self.write_int(v as i64)
    }

    fn emit_f64(&mut self, v: f64) -> CborResult<()> {
        no_string_key!(self, Type::Float64);
        let mut buf = [(7 << 5) | 27, 0, 0, 0, 0, 0, 0, 0, 0];
        <BigEndian as ByteOrder>::write_f64(&mut buf[1..], v);
        fromerr!(self.buf.write_all(&buf))
    }

    fn emit_f32(&mut self, v: f32) -> CborResult<()> {
        no_string_key!(self, Type::Float32);
        let mut buf = [(7 << 5) | 26, 0, 0, 0, 0];
        <BigEndian as ByteOrder>::write_f32(&mut buf[1..], v);
        fromerr!(self.buf.write_all(&buf))
    }

    fn emit_bool(&mut self, v: bool) -> CborResult<()> {
        no_string_key!(self, Type::Bool);
        let n = if v { 21 } else { 20 };
        fromerr!(self.buf.write_all(&[(7 << 5) | n]))
    }

    fn emit_char(&mut self, v: char) -> CborResult<()> {
        no_string_key!(self, Type::UInt32);
        self.emit_u32(v as u32)
    }

    fn emit_str(&mut self, v: &str) -> CborResult<()> {
        try!(self.write_num(3, v.len() as u64));
        fromerr!(self.buf.write_all(v.as_bytes()))
    }

    fn emit_enum<F>(&mut self, _name: &str, f: F) -> CborResult<()>
            where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        f(self)
    }

    fn emit_enum_variant<F>(
        &mut self,
        v_name: &str,
        _v_id: usize,
        len: usize,
        f: F,
    ) -> CborResult<()>
    where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        if len == 0 {
            return self.emit_str(v_name);
        }
        no_string_key!(self);
        try!(self.write_num(5, 1));
        try!(self.emit_str(v_name));
        try!(self.write_num(4, len as u64));
        f(self)
    }

    fn emit_enum_variant_arg<F>(&mut self, _idx: usize, f: F) -> CborResult<()>
            where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        no_string_key!(self);
        f(self)
    }

    fn emit_enum_struct_variant<F>(
        &mut self,
        v_name: &str,
        v_id: usize,
        len: usize,
        f: F,
    ) -> CborResult<()>
    where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        no_string_key!(self);
        self.emit_enum_variant(v_name, v_id, len, f)
    }

    fn emit_enum_struct_variant_field<F>(
        &mut self,
        _f_name: &str,
        idx: usize,
        f: F,
    ) -> CborResult<()>
    where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        no_string_key!(self);
        self.emit_enum_variant_arg(idx, f)
    }

    fn emit_struct<F>(
        &mut self,
        name: &str,
        len: usize,
        f: F,
    ) -> CborResult<()>
    where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        no_string_key!(self, Type::Map);
        match name {
            "CborTag" => {
                self.tag = true;
                let v = f(self);
                self.tag = false;
                return v;
            }
            "CborTagEncode" => {
                self.tag = true;
                let v = f(self);
                self.tag = false;
                return v;
            }
            "CborBytes" => { self.byte_string = true; }
            _ => { try!(self.write_num(5, len as u64)); }
        }
        f(self)
    }

    fn emit_struct_field<F>(
        &mut self,
        f_name: &str,
        _f_idx: usize,
        f: F,
    ) -> CborResult<()>
    where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        no_string_key!(self);
        if !self.byte_string && !self.is_tag_field(f_name) {
            try!(self.emit_str(f_name));
        }
        f(self)
    }

    fn emit_tuple<F>(&mut self, len: usize, f: F) -> CborResult<()>
            where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        no_string_key!(self, Type::Array);
        self.emit_seq(len, f)
    }

    fn emit_tuple_arg<F>(&mut self, idx: usize, f: F) -> CborResult<()>
            where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        no_string_key!(self);
        self.emit_seq_elt(idx, f)
    }

    fn emit_tuple_struct<F>(
        &mut self,
        _name: &str,
        len: usize,
        f: F,
    ) -> CborResult<()>
    where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        no_string_key!(self, Type::Array);
        self.emit_seq(len, f)
    }

    fn emit_tuple_struct_arg<F>(&mut self, idx: usize, f: F) -> CborResult<()>
            where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        no_string_key!(self);
        self.emit_seq_elt(idx, f)
    }

    fn emit_option<F>(&mut self, f: F) -> CborResult<()>
            where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        no_string_key!(self);
        f(self)
    }

    fn emit_option_none(&mut self) -> CborResult<()> {
        no_string_key!(self);
        self.emit_nil()
    }

    fn emit_option_some<F>(&mut self, f: F) -> CborResult<()>
            where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        no_string_key!(self);
        f(self)
    }

    fn emit_seq<F>(&mut self, len: usize, f: F) -> CborResult<()>
            where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        no_string_key!(self, Type::Array);
        if self.byte_string {
            try!(self.write_num(2, len as u64));
            let v = f(self);
            self.byte_string = false;
            return v;
        }
        try!(self.write_num(4, len as u64));
        f(self)
    }

    fn emit_seq_elt<F>(&mut self, _idx: usize, f: F) -> CborResult<()>
            where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        no_string_key!(self);
        f(self)
    }

    fn emit_map<F>(&mut self, len: usize, f: F) -> CborResult<()>
            where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        no_string_key!(self, Type::Map);
        try!(self.write_num(5, len as u64));
        f(self)
    }

    fn emit_map_elt_key<F>(&mut self, _idx: usize, f: F) -> CborResult<()>
            where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        no_string_key!(self);
        self.emitting_key = true;
        let r = f(self);
        self.emitting_key = false;
        r
    }

    fn emit_map_elt_val<F>(&mut self, _idx: usize, f: F) -> CborResult<()>
            where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        no_string_key!(self);
        f(self)
    }
}
