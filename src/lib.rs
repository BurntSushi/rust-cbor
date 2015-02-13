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
use std::old_io::Reader as IoReader;

pub use decoder::{
    CborDecodable, Decoder,
    ByteString,
};
pub use reader::Reader;

// A trivial logging macro. No reason to pull in `log`, which has become
// difficult to use in tests.
macro_rules! lg {
    ($($arg:tt)*) => ({
        let _ = ::std::old_io::stderr().write_str(&*format!($($arg)*));
        let _ = ::std::old_io::stderr().write_str("\n");
    });
}

macro_rules! fromerr { ($e:expr) => ($e.map_err(FromError::from_error)); }

pub type CborResult<T> = Result<T, CborError>;
type ReadResult<T> = Result<T, ReadError>;

#[derive(Debug)]
pub enum CborError {
    Io(IoError),
    Decode(ReadError), // decoder loses byte offset information :-(
    AtOffset { kind: ReadError, offset: usize },
}

#[derive(Debug)]
pub enum ReadError {
    TypeMismatch { expected: Type, got: Type },
    InvalidAddValue { ty: Type, val: u8 },
    Unassigned { major: u8, add: u8 },
    Reserved { major: u8, add: u8 },
    Other(String),
}

impl FromError<IoError> for CborError {
    fn from_error(err: IoError) -> CborError { CborError::Io(err) }
}

impl ReadError {
    fn mismatch(expected: Type, got: &Cbor) -> ReadError {
        ReadError::ty_mismatch(expected, got.typ())
    }

    fn ty_mismatch(expected: Type, got: Type) -> ReadError {
        ReadError::TypeMismatch { expected: expected, got: got }
    }
}

#[derive(Copy, Debug, PartialEq)]
pub enum Type {
    UInt, UInt8, UInt16, UInt32, UInt64,
    Int, Int8, Int16, Int32, Int64,
    Float, Float16, Float32, Float64,
    Bytes, Unicode, Array, Map, Tag,
    Any, Null, Undefined, Bool, Break,
}

#[derive(Debug)]
pub enum Cbor {
    Break, // does this really belong here?
    Undefined,
    Null,
    Bool(bool),
    Unsigned(CborUnsigned),
    Signed(CborSigned),
    Float(CborFloat),
    Bytes(Vec<u8>),
    Unicode(String),
    Array(Vec<Cbor>),
    Map(HashMap<String, Cbor>),
    Tag { tag: u64, data: Box<Cbor> },
}

#[derive(Copy, Debug)]
pub enum CborUnsigned { UInt8(u8), UInt16(u16), UInt32(u32), UInt64(u64) }
#[derive(Copy, Debug)]
pub enum CborSigned { Int8(i8), Int16(i16), Int32(i32), Int64(i64) }
#[derive(Copy, Debug)]
pub enum CborFloat { Float16(f32), Float32(f32), Float64(f64) }

impl Cbor {
    fn typ(&self) -> Type {
        match *self {
            Cbor::Break => Type::Break,
            Cbor::Undefined => Type::Undefined,
            Cbor::Null => Type::Null,
            Cbor::Bool(_) => Type::Bool,
            Cbor::Unsigned(v) => v.typ(),
            Cbor::Signed(v) => v.typ(),
            Cbor::Float(v) => v.typ(),
            Cbor::Bytes(_) => Type::Bytes,
            Cbor::Unicode(_) => Type::Unicode,
            Cbor::Array(_) => Type::Array,
            Cbor::Map(_) => Type::Map,
            Cbor::Tag { .. } => Type::Tag,
        }
    }
}

impl CborUnsigned {
    fn typ(self) -> Type {
        match self {
            CborUnsigned::UInt8(_) => Type::UInt8,
            CborUnsigned::UInt16(_) => Type::UInt16,
            CborUnsigned::UInt32(_) => Type::UInt32,
            CborUnsigned::UInt64(_) => Type::UInt64,
        }
    }

    fn to_usize(self) -> ReadResult<usize> {
        // It should be possible for this to fail. e.g., Converting a
        // UInt64 to a usize when usize is 32 bits.
        Ok(match self {
            CborUnsigned::UInt8(v) => v as usize,
            CborUnsigned::UInt16(v) => v as usize,
            CborUnsigned::UInt32(v) => v as usize,
            CborUnsigned::UInt64(v) => v as usize,
        })
    }

    fn to_u64(self) -> ReadResult<u64> {
        // I don't think this can fail, but it's convenient for it to have
        // the same return type as all of the other integer conversions. ---AG
        Ok(match self {
            CborUnsigned::UInt8(v) => v as u64,
            CborUnsigned::UInt16(v) => v as u64,
            CborUnsigned::UInt32(v) => v as u64,
            CborUnsigned::UInt64(v) => v,
        })
    }

    fn to_u32(self) -> ReadResult<u32> {
        Ok(match self {
            CborUnsigned::UInt8(v) => v as u32,
            CborUnsigned::UInt16(v) => v as u32,
            CborUnsigned::UInt32(v) => v as u32,
            _ => return Err(ReadError::ty_mismatch(Type::UInt32, self.typ())),
        })
    }

    fn to_u16(self) -> ReadResult<u16> {
        Ok(match self {
            CborUnsigned::UInt8(v) => v as u16,
            CborUnsigned::UInt16(v) => v as u16,
            _ => return Err(ReadError::ty_mismatch(Type::UInt16, self.typ())),
        })
    }

    fn to_u8(self) -> ReadResult<u8> {
        Ok(match self {
            CborUnsigned::UInt8(v) => v as u8,
            _ => return Err(ReadError::ty_mismatch(Type::UInt8, self.typ())),
        })
    }
}

impl CborSigned {
    fn typ(self) -> Type {
        match self {
            CborSigned::Int8(_) => Type::Int8,
            CborSigned::Int16(_) => Type::Int16,
            CborSigned::Int32(_) => Type::Int32,
            CborSigned::Int64(_) => Type::Int64,
        }
    }

    fn to_isize(self) -> ReadResult<isize> {
        // It should be possible for this to fail. e.g., Converting a
        // UInt64 to a usize when usize is 32 bits.
        Ok(match self {
            CborSigned::Int8(v) => v as isize,
            CborSigned::Int16(v) => v as isize,
            CborSigned::Int32(v) => v as isize,
            CborSigned::Int64(v) => v as isize,
        })
    }

    fn to_i64(self) -> ReadResult<i64> {
        // I don't think this can fail, but it's convenient for it to have
        // the same return type as all of the other integer conversions. ---AG
        Ok(match self {
            CborSigned::Int8(v) => v as i64,
            CborSigned::Int16(v) => v as i64,
            CborSigned::Int32(v) => v as i64,
            CborSigned::Int64(v) => v,
        })
    }

    fn to_i32(self) -> ReadResult<i32> {
        Ok(match self {
            CborSigned::Int8(v) => v as i32,
            CborSigned::Int16(v) => v as i32,
            CborSigned::Int32(v) => v as i32,
            _ => return Err(ReadError::ty_mismatch(Type::Int32, self.typ())),
        })
    }

    fn to_i16(self) -> ReadResult<i16> {
        Ok(match self {
            CborSigned::Int8(v) => v as i16,
            CborSigned::Int16(v) => v as i16,
            _ => return Err(ReadError::ty_mismatch(Type::Int16, self.typ())),
        })
    }

    fn to_i8(self) -> ReadResult<i8> {
        Ok(match self {
            CborSigned::Int8(v) => v as i8,
            _ => return Err(ReadError::ty_mismatch(Type::Int8, self.typ())),
        })
    }
}

impl CborFloat {
    fn typ(self) -> Type {
        match self {
            CborFloat::Float16(_) => Type::Float16,
            CborFloat::Float32(_) => Type::Float32,
            CborFloat::Float64(_) => Type::Float64,
        }
    }

    fn to_f64(self) -> ReadResult<f64> {
        // I don't think this can fail, but it's convenient for it to have
        // the same return type as all of the other number conversions. ---AG
        Ok(match self {
            CborFloat::Float16(v) => v as f64,
            CborFloat::Float32(v) => v as f64,
            CborFloat::Float64(v) => v,
        })
    }

    fn to_f32(self) -> ReadResult<f32> {
        // I don't think this can fail, but it's convenient for it to have
        // the same return type as all of the other number conversions. ---AG
        Ok(match self {
            CborFloat::Float16(v) => v,
            CborFloat::Float32(v) => v,
            _ => return Err(ReadError::ty_mismatch(Type::Float32, self.typ())),
        })
    }
}

mod decoder;
mod encoder;
mod reader;


#[cfg(test)]
mod test {
    use std::collections::HashMap;
    use rustc_serialize::Decodable;
    use {Reader, Decoder};
    use ByteString;

    #[test]
    fn scratch() {
        // let bytes = vec![25, 1, 5];
        let bytes = vec![24, 5];

        // -500
        // let bytes = vec![0b001_11001, 0x01, 0xf3];

        // [256, -500]
        // let bytes = vec![0x82, 0x19, 0x01, 0x00, 0x39, 0x01, 0xf3];

        // [-256, -500]
        // let bytes = vec![0x82, 0x38, 0xff, 0x39, 0x01, 0xf3];

        // true
        // let bytes = vec![0xf4];

        // 1.5
        // let bytes = vec![0xfb, 0x3f, 0xf8, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0];

        // u'b'
        // let bytes = vec![0x61, 0x62];

        // b'b'
        // let bytes = vec![0x41, 0x62];

        // {'a': 1}
        // let bytes = vec![0xa1, 0x61, 0x61, 0x01];

        // (2 ** 64) - 1
        // let bytes = vec![0x1b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff];

        // Tag(500, [1, 500, 100000])
        // ['0xd9', '0x1', '0xf4', '0x83', '0x1', '0x19', '0x1', '0xf4', '0x1a', '0x0', '0x1', '0x86', '0xa0']
        let bytes = vec![0xd9, 0x01, 0xf4, 0x83, 0x01, 0x19, 0x01, 0xf4,
                         0x1a, 0x00, 0x01, 0x86, 0xa0];

        let mut rdr = Reader::from_bytes(bytes);
        // let val = rdr.read().unwrap();
        // let v: String = Decodable::decode(&mut Decoder::new(val)).unwrap();
        // let v: ByteString = rdr.decode().unwrap();
        // let v: Vec<i16> = rdr.decode().unwrap();
        // let v: u64 = rdr.decode().unwrap();
        // let v: i64 = rdr.decode().unwrap();
        // let v: f64 = rdr.decode().unwrap();
        // let v: String = rdr.decode().unwrap();
        // let v: ByteString = rdr.decode().unwrap();
        // let v: HashMap<String, i32> = rdr.decode().unwrap();
        // let v: Vec<f32> = rdr.decode().unwrap();
        // let v: bool = rdr.decode().unwrap();

        // lg!("{:?}", v);
        lg!("{:?}", rdr.read().unwrap());
    }
}
