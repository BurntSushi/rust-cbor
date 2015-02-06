#![crate_name = "cbor"]
#![doc(html_root_url = "http://burntsushi.net/rustdoc/cbor")]

#![allow(dead_code, unused_imports, unused_variables,
         missing_copy_implementations)]

#![feature(core, io)]

extern crate byteorder;

use std::borrow::IntoCow;
use std::collections::HashMap;
use std::error::FromError;
use std::old_io::{IoError, IoResult, MemReader};

use byteorder::{ReaderBytesExt, BigEndian};

use self::Cbor::*;
use self::CborUnsigned::*;
use self::CborSigned::*;
use self::CborFloat::*;
use self::CborError::*;

// A trivial logging macro. No reason to pull in `log`, which has become
// difficult to use in tests.
macro_rules! lg {
    ($($arg:tt)*) => ({
        let _ = ::std::old_io::stderr().write_str(&*format!($($arg)*));
        let _ = ::std::old_io::stderr().write_str("\n");
    });
}

type CborResult<T> = Result<T, CborError>;

#[derive(Debug)]
pub enum CborError {
    InvalidAddInfoForType,
    Io(IoError),
}

impl FromError<IoError> for CborError {
    fn from_error(err: IoError) -> CborError { CborError::Io(err) }
}

#[derive(Debug)]
pub enum Cbor {
    Unsigned(CborUnsigned),
    Signed(CborSigned),
    Float(CborFloat),
    Bytes(Vec<u8>),
    Unicode(String),
    Array(Vec<Cbor>),
    Map(HashMap<String, Cbor>),
    Tag(Box<Cbor>),
}

#[derive(Copy, Debug)]
pub enum CborUnsigned { UInt8(u8), UInt16(u16), UInt32(u32), UInt64(u64) }
#[derive(Copy, Debug)]
pub enum CborSigned { Int8(i8), Int16(i16), Int32(i32), Int64(i64) }
#[derive(Copy, Debug)]
pub enum CborFloat { Float32(f32), Float64(f64) }

// trait CborBytes {
    // fn serialize<W: Writer>(&self, wtr: W) -> IoResult<()>;
    // fn deserialize<R: Reader>(rdr: R) -> IoResult<Self>;
// }

impl Cbor {
    fn from_bytes<'a, T>(bytes: T) -> CborResult<Cbor>
            where T: IntoCow<'a, Vec<u8>, [u8]> {
        Cbor::from_reader(MemReader::new(bytes.into_cow().into_owned()))
    }
    fn from_reader<R: ReaderBytesExt>(mut rdr: R) -> CborResult<Cbor> {
        let init = try!(rdr.read_byte());
        let (ty, add) = (major_type(init), additional(init));
        Ok(match ty {
            0 => match add {
                0...23 => Unsigned(UInt8(add)),
                24 => Unsigned(UInt8(try!(rdr.read_byte()))),
                25 => Unsigned(UInt16(try!(rdr.read_u16::<BigEndian>()))),
                26 => Unsigned(UInt32(try!(rdr.read_u32::<BigEndian>()))),
                27 => Unsigned(UInt64(try!(rdr.read_u64::<BigEndian>()))),
                _ => return Err(CborError::InvalidAddInfoForType),
            },
            // This is truly unreachable since `ty` is contrained to 3 bits.
            _ => unreachable!(),
        })
    }
}

#[inline] fn major_type(b: u8) -> u8 { (b & 0b111_00000) >> 5 }
#[inline] fn additional(b: u8) -> u8 { b & 0b000_11111 }

#[cfg(test)]
mod test {
    use Cbor;

    #[test]
    fn scratch() {
        lg!("{:?}", Cbor::from_bytes(vec![25, 1, 255]).unwrap());
    }
}
