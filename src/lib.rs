#![crate_name = "cbor"]
#![doc(html_root_url = "http://burntsushi.net/rustdoc/cbor")]

#![allow(dead_code, unused_imports, unused_variables,
         missing_copy_implementations)]

#![feature(core, io)]

extern crate byteorder;
extern crate "rustc-serialize" as rustc_serialize;

use std::borrow::{IntoCow, ToOwned};
use std::char;
use std::collections::HashMap;
use std::error::FromError;
use std::iter::repeat;
use std::old_io::{IoError, IoResult, MemReader};

use byteorder::{ReaderBytesExt, BigEndian};
use rustc_serialize::{Decodable, Decoder};

use self::CborError::*;
use self::DecoderError::*;

// A trivial logging macro. No reason to pull in `log`, which has become
// difficult to use in tests.
macro_rules! lg {
    ($($arg:tt)*) => ({
        let _ = ::std::old_io::stderr().write_str(&*format!($($arg)*));
        let _ = ::std::old_io::stderr().write_str("\n");
    });
}

macro_rules! fromerr { ($e:expr) => ($e.map_err(FromError::from_error)); }

type CborResult<T> = Result<T, CborError>;

#[derive(Debug)]
pub enum CborError {
    Io(IoError),
    AtOffset { kind: DecoderError, offset: usize },
}

#[derive(Debug)]
pub enum DecoderError {
    TypeError { expected: Type, got: Type },
    InvalidAddValue { ty: Type, val: u8 },
    Other(String),
}

impl FromError<IoError> for CborError {
    fn from_error(err: IoError) -> CborError { CborError::Io(err) }
}

impl CborError {
    fn patch_got_type(self, got: Type) -> CborError {
        match self {
            AtOffset { kind: TypeError { expected, .. }, offset } => {
                AtOffset {
                    kind: TypeError { expected: expected, got: got },
                    offset: offset,
                }
            }
            err => err,
        }
    }
}

pub struct CborDecoder<R> {
    rdr: CborReader<R>,
}

impl CborDecoder<MemReader> {
    fn from_bytes<'a, T>(bytes: T) -> CborDecoder<MemReader>
            where T: IntoCow<'a, Vec<u8>, [u8]> {
        CborDecoder::from_reader(MemReader::new(bytes.into_cow().into_owned()))
    }
}

impl<R: Reader> CborDecoder<R> {
    fn from_reader(rdr: R) -> CborDecoder<R> {
        CborDecoder { rdr: CborReader::new(rdr) }
    }

    fn decode<D>(&mut self) -> CborResult<D> where D: CborDecodable {
        CborDecodable::cbor_decode(self)
    }

    fn rustc_decode<D>(&mut self) -> CborResult<D> where D: Decodable {
        Decodable::decode(self)
    }

    fn read_type<F, T>(&mut self, con: F) -> CborResult<Typed<T>>
            where F: FnOnce(u8) -> Result<Typed<T>, DecoderError> {
        let b = try!(self.rdr.read_byte());
        con(b).map_err(|err| self.errat(err))
    }

    fn read_len(&mut self, ty: TypedNumber) -> CborResult<usize> {
        self.next_u64(ty).map(|n| n as usize)
    }

    fn next_u64(&mut self, ty: TypedNumber) -> CborResult<u64> {
        Ok(match ty {
            Typed(Type::UInt8, Some(add)) => add as u64,
            Typed(Type::UInt8, None) => try!(self.rdr.read_byte()) as u64,
            Typed(Type::UInt16, None) =>
                try!(self.rdr.read_u16::<BigEndian>()) as u64,
            Typed(Type::UInt32, None) =>
                try!(self.rdr.read_u32::<BigEndian>()) as u64,
            Typed(Type::UInt64, None) =>
                try!(self.rdr.read_u64::<BigEndian>()),
            Typed(ty, _) => return Err(self.errty(Type::UInt64, ty)),
        })
    }

    fn next_u32(&mut self, ty: TypedNumber) -> CborResult<u32> {
        Ok(match ty {
            Typed(Type::UInt8, Some(add)) => add as u32,
            Typed(Type::UInt8, None) => try!(self.rdr.read_byte()) as u32,
            Typed(Type::UInt16, None) =>
                try!(self.rdr.read_u16::<BigEndian>()) as u32,
            Typed(Type::UInt32, None) =>
                try!(self.rdr.read_u32::<BigEndian>()),
            Typed(ty, _) => return Err(self.errty(Type::UInt32, ty)),
        })
    }

    fn next_u16(&mut self, ty: TypedNumber) -> CborResult<u16> {
        Ok(match ty {
            Typed(Type::UInt8, Some(add)) => add as u16,
            Typed(Type::UInt8, None) => try!(self.rdr.read_byte()) as u16,
            Typed(Type::UInt16, None) =>
                try!(self.rdr.read_u16::<BigEndian>()),
            Typed(ty, _) => return Err(self.errty(Type::UInt16, ty)),
        })
    }

    fn next_u8(&mut self, ty: TypedNumber) -> CborResult<u8> {
        Ok(match ty {
            Typed(Type::UInt8, Some(add)) => add,
            Typed(Type::UInt8, None) => try!(self.rdr.read_byte()),
            Typed(ty, _) => return Err(self.errty(Type::UInt8, ty)),
        })
    }
}

impl<R: Reader> CborDecoder<R> {
    fn errat(&self, err: DecoderError) -> CborError {
        AtOffset { kind: err, offset: self.rdr.last_offset }
    }

    fn errty(&self, expected: Type, got: Type) -> CborError {
        self.errat(TypeError { expected: expected, got: got })
    }

    fn errstr(&self, s: String) -> CborError {
        self.errat(Other(s))
    }
}

impl<R: Reader> Decoder for CborDecoder<R> {
    type Error = CborError;

    fn error(&mut self, err: &str) -> CborError {
        self.errat(Other(err.to_owned()))
    }

    fn read_nil(&mut self) -> CborResult<()> {
        unreachable!()
    }

    fn read_usize(&mut self) -> CborResult<usize> {
        // What happens if we're reading a 64 bit integer on a 32 bit
        // system? ---AG
        self.read_u64().map(|n| n as usize)
    }

    fn read_u64(&mut self) -> CborResult<u64> {
        self.read_type(Typed::uint_type).and_then(|ty| self.next_u64(ty))
    }

    fn read_u32(&mut self) -> CborResult<u32> {
        self.read_type(Typed::uint_type).and_then(|ty| self.next_u32(ty))
    }

    fn read_u16(&mut self) -> CborResult<u16> {
        self.read_type(Typed::uint_type).and_then(|ty| self.next_u16(ty))
    }

    fn read_u8(&mut self) -> CborResult<u8> {
        self.read_type(Typed::uint_type).and_then(|ty| self.next_u8(ty))
    }

    fn read_isize(&mut self) -> CborResult<isize> {
        // What happens if we're reading a 64 bit integer on a 32 bit
        // system? ---AG
        self.read_i64().map(|n| n as isize)
    }

    fn read_i64(&mut self) -> CborResult<i64> {
        let ity = try!(self.read_type(Typed::int_type));
        let n = try!(self.next_u64(ity.mapty(|t| t.to_uint()))
                         .map_err(|err| err.patch_got_type(ity.0))) as i64;
        Ok(if ity.is_uint() { n } else { -1 - n })
    }

    fn read_i32(&mut self) -> CborResult<i32> {
        let ity = try!(self.read_type(Typed::int_type));
        let n = try!(self.next_u32(ity.mapty(|t| t.to_uint()))
                         .map_err(|err| err.patch_got_type(ity.0))) as i32;
        Ok(if ity.is_uint() { n } else { -1 - n })
    }

    fn read_i16(&mut self) -> CborResult<i16> {
        let ity = try!(self.read_type(Typed::int_type));
        let n = try!(self.next_u16(ity.mapty(|t| t.to_uint()))
                         .map_err(|err| err.patch_got_type(ity.0))) as i16;
        Ok(if ity.is_uint() { n } else { -1 - n })
    }

    fn read_i8(&mut self) -> CborResult<i8> {
        let ity = try!(self.read_type(Typed::int_type));
        let n = try!(self.next_u8(ity.mapty(|t| t.to_uint()))
                         .map_err(|err| err.patch_got_type(ity.0))) as i8;
        Ok(if ity.is_uint() { n } else { -1 - n })
    }

    fn read_bool(&mut self) -> CborResult<bool> {
        unreachable!()
    }

    fn read_f64(&mut self) -> CborResult<f64> {
        unreachable!()
    }

    fn read_f32(&mut self) -> CborResult<f32> {
        unreachable!()
    }

    fn read_char(&mut self) -> CborResult<char> {
        let n = try!(self.read_u32());
        match char::from_u32(n) {
            Some(c) => Ok(c),
            None => Err(self.errstr(format!(
                "Could not convert '{:?}' to Unicode scalar value.", n))),
        }
    }

    fn read_str(&mut self) -> CborResult<String> {
        let ty = try!(self.read_type(Typed::list_type));
        if ty.0 != Type::String {
            Err(self.errty(Type::String, ty.0))
        } else {
            let len = try!(self.read_len(ty.1));
            let mut buf: Vec<u8> = repeat(0).take(len).collect();
            try!(read_full(&mut self.rdr, &mut buf));
            String::from_utf8(buf)
                   .map_err(|err| self.errstr(err.utf8_error().to_string()))
        }
    }

    fn read_enum<T, F>(&mut self, name: &str, f: F) -> CborResult<T>
            where F: FnOnce(&mut CborDecoder<R>) -> CborResult<T> {
        unreachable!()
    }

    fn read_enum_variant<T, F>(
        &mut self,
        names: &[&str],
        f: F,
    ) -> CborResult<T>
    where F: FnMut(&mut CborDecoder<R>, usize) -> CborResult<T> {
        unreachable!()
    }

    fn read_enum_variant_arg<T, F>(
        &mut self,
        a_idx: usize,
        f: F,
    ) -> CborResult<T>
    where F: FnOnce(&mut CborDecoder<R>) -> CborResult<T> {
        unreachable!()
    }

    fn read_enum_struct_variant<T, F>(
        &mut self,
        names: &[&str],
        f: F,
    ) -> CborResult<T>
    where F: FnMut(&mut CborDecoder<R>, usize) -> CborResult<T> {
        unreachable!()
    }

    fn read_enum_struct_variant_field<T, F>(
        &mut self,
        f_name: &str,
        f_idx: usize,
        f: F,
    ) -> CborResult<T>
    where F: FnOnce(&mut CborDecoder<R>) -> CborResult<T> {
        unreachable!()
    }

    fn read_struct<T, F>(
        &mut self,
        s_name: &str,
        len: usize,
        f: F,
    ) -> CborResult<T>
    where F: FnOnce(&mut CborDecoder<R>) -> CborResult<T> {
        unreachable!()
    }

    fn read_struct_field<T, F>(
        &mut self,
        f_name: &str,
        f_idx: usize,
        f: F,
    ) -> CborResult<T>
    where F: FnOnce(&mut CborDecoder<R>) -> CborResult<T> {
        unreachable!()
    }

    fn read_tuple<T, F>(
        &mut self,
        len: usize,
        f: F,
    ) -> CborResult<T>
    where F: FnOnce(&mut CborDecoder<R>) -> CborResult<T> {
        unreachable!()
    }

    fn read_tuple_arg<T, F>(
        &mut self,
        a_idx: usize,
        f: F,
    ) -> CborResult<T>
    where F: FnOnce(&mut CborDecoder<R>) -> CborResult<T> {
        unreachable!()
    }

    fn read_tuple_struct<T, F>(
        &mut self,
        s_name: &str,
        len: usize,
        f: F,
    ) -> CborResult<T>
    where F: FnOnce(&mut CborDecoder<R>) -> CborResult<T> {
        unreachable!()
    }

    fn read_tuple_struct_arg<T, F>(
        &mut self,
        a_idx: usize,
        f: F,
    ) -> CborResult<T>
    where F: FnOnce(&mut CborDecoder<R>) -> CborResult<T> {
        unreachable!()
    }

    fn read_option<T, F>(&mut self, f: F) -> CborResult<T>
            where F: FnMut(&mut CborDecoder<R>, bool) -> CborResult<T> {
        unreachable!()
    }

    fn read_seq<T, F>(&mut self, f: F) -> CborResult<T>
            where F: FnOnce(&mut CborDecoder<R>, usize) -> CborResult<T> {
        let ty = try!(self.read_type(Typed::list_type));
        if ty.0 != Type::Array {
            Err(self.errty(Type::Array, ty.0))
        } else {
            let len = try!(self.read_len(ty.1));
            f(self, len)
        }
    }

    fn read_seq_elt<T, F>(&mut self, idx: usize, f: F) -> CborResult<T>
            where F: FnOnce(&mut CborDecoder<R>) -> CborResult<T> {
        f(self)
    }

    fn read_map<T, F>(&mut self, f: F) -> CborResult<T>
            where F: FnOnce(&mut CborDecoder<R>, usize) -> CborResult<T> {
        unreachable!()
    }

    fn read_map_elt_key<T, F>(&mut self, idx: usize, f: F) -> CborResult<T>
            where F: FnOnce(&mut CborDecoder<R>) -> CborResult<T> {
        unreachable!()
    }

    fn read_map_elt_val<T, F>(&mut self, idx: usize, f: F) -> CborResult<T>
            where F: FnOnce(&mut CborDecoder<R>) -> CborResult<T> {
        unreachable!()
    }
}

#[derive(Debug)]
pub struct ByteString(Vec<u8>);

impl CborDecodable for ByteString {
    fn cbor_decode<R: Reader>(d: &mut CborDecoder<R>) -> CborResult<ByteString> {
        let ty = try!(d.read_type(Typed::list_type));
        if ty.0 != Type::Bytes {
            Err(d.errty(Type::Bytes, ty.0))
        } else {
            let len = try!(d.read_len(ty.1));
            let mut buf: Vec<u8> = repeat(0).take(len).collect();
            try!(read_full(&mut d.rdr, &mut buf));
            Ok(ByteString(buf))
        }
    }
}

trait CborDecodable {
    fn cbor_decode<R: Reader>(d: &mut CborDecoder<R>) -> CborResult<Self>;
}

impl<D: Decodable> CborDecodable for D {
    fn cbor_decode<R: Reader>(d: &mut CborDecoder<R>) -> CborResult<D> {
        d.rustc_decode()
    }
}

#[derive(Copy)]
pub struct Typed<T>(Type, T);

type TypedNumber = Typed<Option<u8>>;

#[derive(Copy, Debug, PartialEq)]
pub enum Type {
    UInt, UInt8, UInt16, UInt32, UInt64,
    Int, Int8, Int16, Int32, Int64,
    Float32, Float64,
    Bytes, String, Array, Map, Tag,
}

impl Type {
    fn to_uint(self) -> Type {
        match self {
            Type::Int => Type::UInt,
            Type::Int8 => Type::UInt8,
            Type::Int16 => Type::UInt16,
            Type::Int32 => Type::UInt32,
            Type::Int64 => Type::UInt64,
            ty => ty,
        }
    }

    fn is_uint(self) -> bool {
        match self {
            Type::UInt | Type::UInt8 | Type::UInt16
            | Type::UInt32 | Type::UInt64 => true,
            _ => false,
        }
    }
}

impl<T> Typed<T> {
    fn to_uint(self) -> Typed<T> { self.mapty(|ty| ty.to_uint()) }

    fn is_uint(self) -> bool { self.0.is_uint() }

    fn mapty<F>(self, f: F) -> Typed<T> where F: FnOnce(Type) -> Type {
        Typed(f(self.0), self.1)
    }

    fn map<F, R>(self, f: F) -> Typed<R> where F: FnOnce(T) -> R {
        Typed(self.0, f(self.1))
    }
}

impl Typed<Option<u8>> {
    fn uint_type(b: u8) -> Result<TypedNumber, DecoderError> {
        match (b & 0b111_00000) >> 5 {
            0 => Typed::extract_uint_type(b),
            ty_num => return Err(Other(format!(
                "Expected a 'UInt' type, but got a major type of '{:?}'",
                ty_num))),
        }
    }

    fn int_type(b: u8) -> Result<TypedNumber, DecoderError> {
        match (b & 0b111_00000) >> 5 {
            0 => Typed::extract_uint_type(b),
            1 => Typed::extract_int_type(b),
            ty_num => Err(Other(format!(
                "Expected a 'Int' or 'UInt' type, \
                 but got a major type of '{:?}'", ty_num))),
        }
    }

    fn extract_uint_type(b: u8) -> Result<TypedNumber, DecoderError> {
        Ok(match b & 0b000_11111 {
            0...23 => Typed(Type::UInt8, Some(b & 0b000_11111)),
            24 => Typed(Type::UInt8, None),
            25 => Typed(Type::UInt16, None),
            26 => Typed(Type::UInt32, None),
            27 => Typed(Type::UInt64, None),
            val => return Err(InvalidAddValue {ty: Type::UInt, val: val}),
        })
    }

    fn extract_int_type(b: u8) -> Result<TypedNumber, DecoderError> {
        Ok(match b & 0b000_11111 {
            0...23 => Typed(Type::Int8, Some(b & 0b000_11111)),
            24 => Typed(Type::Int8, None),
            25 => Typed(Type::Int16, None),
            26 => Typed(Type::Int32, None),
            27 => Typed(Type::Int64, None),
            val => return Err(InvalidAddValue {ty: Type::Int, val: val}),
        })
    }
}

impl Typed<TypedNumber> {
    fn list_type(b: u8) -> Result<Typed<TypedNumber>, DecoderError> {
        // Converts the major type to "unsigned integer" major type.
        let num_type = |b| Typed::uint_type(b & 0b000_11111);
        Ok(match (b & 0b111_00000) >> 5 {
            2 => Typed(Type::Bytes, try!(num_type(b))),
            3 => Typed(Type::String, try!(num_type(b))),
            4 => Typed(Type::Array, try!(num_type(b))),
            5 => Typed(Type::Map, try!(num_type(b))),
            ty_num => return Err(Other(format!(
                "Expected a list type ('Bytes', 'String', 'Array' or 'Map'), \
                 but got a major type of '{:?}'", ty_num))),
        })
    }
}

struct CborReader<R> {
    rdr: R,
    // used for error reporting
    last_offset: usize,
    bytes_read: usize,
}

impl<R: Reader> Reader for CborReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> IoResult<usize> {
        let n = try!(self.rdr.read(buf));
        self.last_offset = self.bytes_read;
        self.bytes_read += n;
        Ok(n)
    }
}

impl<R: Reader> CborReader<R> {
    fn new(rdr: R) -> CborReader<R> {
        CborReader { rdr: rdr, last_offset: 0, bytes_read: 0 }
    }
}

fn read_full<R: Reader>(rdr: &mut R, buf: &mut [u8]) -> IoResult<()> {
    let mut n = 0us;
    while n < buf.len() {
        n += try!(rdr.read(&mut buf[n..]));
    }
    Ok(())
}

#[cfg(test)]
mod test {
    use CborDecoder;
    use ByteString;

    #[test]
    fn scratch() {
        // let bytes = vec![25, 1, 5];
        // let bytes = vec![24, 5];

        // -500
        // let bytes = vec![0b001_11001, 0x01, 0xf3];

        // [256, -500]
        // let bytes = vec![0x82, 0x19, 0x01, 0x00, 0x39, 0x01, 0xf3];

        // [-256, -500]
        // let bytes = vec![0x82, 0x38, 0xff, 0x39, 0x01, 0xf3];

        // u'a'
        // let bytes = vec![0x61, 0x62];

        // b'a'
        let bytes = vec![0x41, 0x62];

        let mut rdr = CborDecoder::from_bytes(bytes);
        // let v: Vec<i16> = rdr.decode().unwrap();
        // let v: i64 = rdr.decode().unwrap();
        // let v: String = rdr.decode().unwrap();
        let v: ByteString = rdr.decode().unwrap();
        lg!("{:?}", v);
    }
}
