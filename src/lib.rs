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
use std::old_io::Writer as IoWriter;
use rustc_serialize::Decoder as RustcDecoder;
use rustc_serialize::Encoder as RustcEncoder;
use rustc_serialize::{Decodable, Encodable};

pub use decoder::Decoder;
pub use encoder::Encoder;

// A trivial logging macro. No reason to pull in `log`, which has become
// difficult to use in tests.
macro_rules! lg {
    ($($arg:tt)*) => ({
        let _ = ::std::old_io::stderr().write_str(&*format!($($arg)*));
        let _ = ::std::old_io::stderr().write_str("\n");
    });
}

macro_rules! fromerr {
    ($e:expr) => ($e.map_err(::std::error::FromError::from_error));
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Type {
    UInt, UInt8, UInt16, UInt32, UInt64,
    Int, Int8, Int16, Int32, Int64,
    Float, Float16, Float32, Float64,
    Bytes, Unicode, Array, Map, Tag,
    Any, Null, Undefined, Bool, Break,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Cbor {
    Break, // does this really belong here?
    Undefined,
    Null,
    Bool(bool),
    Unsigned(CborUnsigned),
    Signed(CborSigned),
    Float(CborFloat),
    Bytes(CborBytes),
    Unicode(String),
    Array(Vec<Cbor>),
    Map(HashMap<String, Cbor>),
    Tag(CborTag),
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd, RustcDecodable)]
pub enum CborUnsigned { UInt8(u8), UInt16(u16), UInt32(u32), UInt64(u64) }
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd, RustcDecodable)]
pub enum CborSigned { Int8(i8), Int16(i16), Int32(i32), Int64(i64) }
#[derive(Clone, Copy, Debug, PartialEq, PartialOrd, RustcDecodable)]
pub enum CborFloat { Float16(f32), Float32(f32), Float64(f64) }
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, RustcEncodable)]
pub struct CborBytes(pub Vec<u8>);
#[derive(Clone, Debug, PartialEq, RustcEncodable)]
pub struct CborTag { pub tag: u64, pub data: Box<Cbor> }
#[derive(Clone, Debug, PartialEq, RustcEncodable)]
pub struct CborTagEncode<'a, T: 'a> { pub tag: u64, pub data: &'a T }

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
            Cbor::Tag(_) => Type::Tag,
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
        Ok(match self {
            CborFloat::Float16(v) => v,
            CborFloat::Float32(v) => v,
            _ => return Err(ReadError::ty_mismatch(Type::Float32, self.typ())),
        })
    }
}

impl Encodable for Cbor {
    fn encode<E: RustcEncoder>(&self, e: &mut E) -> Result<(), E::Error> {
        match *self {
            // Not sure what to do with `Break` here. I guess if we need to
            // be able to encode, we'll have to add special support for it
            // in the encoder.
            Cbor::Break => unimplemented!(),
            Cbor::Undefined => e.emit_nil(),
            Cbor::Null => e.emit_nil(),
            Cbor::Bool(v) => v.encode(e),
            Cbor::Unsigned(v) => v.encode(e),
            Cbor::Signed(v) => v.encode(e),
            Cbor::Float(v) => v.encode(e),
            Cbor::Bytes(ref v) => v.encode(e),
            Cbor::Unicode(ref v) => v.encode(e),
            Cbor::Array(ref v) => v.encode(e),
            Cbor::Map(ref v) => v.encode(e),
            Cbor::Tag(ref v) => v.encode(e),
        }
    }
}

impl Encodable for CborUnsigned {
    fn encode<E: RustcEncoder>(&self, e: &mut E) -> Result<(), E::Error> {
        match *self {
            CborUnsigned::UInt8(v) => v.encode(e),
            CborUnsigned::UInt16(v) => v.encode(e),
            CborUnsigned::UInt32(v) => v.encode(e),
            CborUnsigned::UInt64(v) => v.encode(e),
        }
    }
}

impl Encodable for CborSigned {
    fn encode<E: RustcEncoder>(&self, e: &mut E) -> Result<(), E::Error> {
        match *self {
            CborSigned::Int8(v) => v.encode(e),
            CborSigned::Int16(v) => v.encode(e),
            CborSigned::Int32(v) => v.encode(e),
            CborSigned::Int64(v) => v.encode(e),
        }
    }
}

impl Encodable for CborFloat {
    fn encode<E: RustcEncoder>(&self, e: &mut E) -> Result<(), E::Error> {
        match *self {
            CborFloat::Float16(v) => v.encode(e),
            CborFloat::Float32(v) => v.encode(e),
            CborFloat::Float64(v) => v.encode(e),
        }
    }
}

impl Decodable for CborBytes {
    fn decode<D: RustcDecoder>(d: &mut D) -> Result<CborBytes, D::Error> {
        Decodable::decode(d).map(CborBytes)
    }
}

pub type CborResult<T> = Result<T, CborError>;
type ReadResult<T> = Result<T, ReadError>;

#[derive(Debug)]
pub enum CborError {
    Io(IoError),
    Decode(ReadError), // decoder loses byte offset information :-(
    Encode(WriteError),
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

#[derive(Debug)]
pub enum WriteError {
    TypeMismatch { expected: Type, got: Type },
    InvalidMapKey { got: Option<Type> },
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

mod decoder;
mod encoder;
mod rustc_decoder;
