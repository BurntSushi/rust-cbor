use std::borrow::{IntoCow, ToOwned};
use std::collections::hash_map::HashMap;
use std::old_io::{IoError, IoResult, MemReader};
use std::old_io::Reader as IoReader;
use std::mem::transmute;

use byteorder::{ReaderBytesExt, BigEndian};
use rustc_serialize::Decodable;

use {
    Cbor, CborUnsigned, CborSigned, CborFloat,
    Type,
    CborResult, CborError, ReadError,
    CborDecodable, Decoder,
};

pub struct Reader<R> {
    rdr: CborReader<R>,
}

impl Reader<MemReader> {
    pub fn from_bytes<'a, T>(bytes: T) -> Reader<MemReader>
            where T: IntoCow<'a, Vec<u8>, [u8]> {
        Reader::from_reader(MemReader::new(bytes.into_cow().into_owned()))
    }
}

impl<R: IoReader> Reader<R> {
    pub fn from_reader(rdr: R) -> Reader<R> {
        Reader { rdr: CborReader::new(rdr) }
    }
}

impl<R: IoReader> Reader<R> {
    fn errat(&self, err: ReadError) -> CborError {
        CborError::AtOffset { kind: err, offset: self.rdr.last_offset }
    }

    fn errty(&self, expected: Type, got: Type) -> CborError {
        self.errat(ReadError::TypeMismatch { expected: expected, got: got })
    }

    fn errstr(&self, s: String) -> CborError {
        self.errat(ReadError::Other(s))
    }
}

impl<R: IoReader> Reader<R> {
    pub fn decode<D>(&mut self) -> CborResult<D> where D: CborDecodable {
        let v = try!(self.read());
        CborDecodable::cbor_decode(&mut Decoder::new(v))
    }

    fn rustc_decode<D>(&mut self) -> CborResult<D> where D: Decodable {
        Decodable::decode(&mut Decoder::new(try!(self.read())))
    }

    pub fn read(&mut self) -> CborResult<Cbor> {
        self.read_data_item(None)
    }

    fn read_data_item(&mut self, first: Option<u8>) -> CborResult<Cbor> {
        let first = match first {
            Some(first) => first,
            None => try!(self.rdr.read_byte()),
        };
        match (first & 0b111_00000) >> 5 {
            0 => self.read_uint(first).map(Cbor::Unsigned),
            1 => self.read_int(first).map(Cbor::Signed),
            2 => self.read_bytes(first),
            3 => self.read_string(first),
            4 => self.read_array(first),
            5 => self.read_map(first),
            6 => self.read_tag(first),
            7 => match first & 0b000_11111 {
                v @ 0...23 => self.read_simple_value(v),
                24 => {
                    let b = try!(self.rdr.read_byte());
                    self.read_simple_value(b)
                }
                25...27 => self.read_float(first).map(Cbor::Float),
                v @ 28...30 =>
                    Err(self.errat(
                        ReadError::Unassigned { major: 7, add: v })),
                31 => Ok(Cbor::Break),
                // Because max(byte & 0b000_11111) == 2^5 - 1 == 31
                _ => unreachable!(),
            },
            // This is truly unreachable because `byte & 0b111_00000 >> 5`
            // can only produce 8 distinct values---each of which are handled
            // above. ---AG
            _ => unreachable!(),
        }
    }

    fn read_simple_value(&mut self, val: u8) -> CborResult<Cbor> {
        Ok(match val {
            v @ 0...19 =>
                return Err(self.errat(
                    ReadError::Unassigned { major: 7, add: v })),
            20 => Cbor::Bool(false),
            21 => Cbor::Bool(true),
            22 => Cbor::Null,
            23 => Cbor::Undefined,
            v @ 24...31 =>
                return Err(self.errat(
                    ReadError::Reserved { major: 7, add: v })),
            v /* 32...255 */ =>
                return Err(self.errat(
                    ReadError::Unassigned { major: 7, add: v })),
        })
    }

    fn read_float(&mut self, first: u8) -> CborResult<CborFloat> {
        Ok(match first & 0b000_11111 {
            25 => {
                // Rust doesn't have a `f16` type, so just read a u16 and
                // cast it to a u32 and then a f32.
                let n = try!(self.rdr.read_u16::<BigEndian>());
                CborFloat::Float16(unsafe { transmute(n as u32) })
            }
            26 => CborFloat::Float32(try!(self.rdr.read_f32::<BigEndian>())),
            27 => CborFloat::Float64(try!(self.rdr.read_f64::<BigEndian>())),
            // Reaching this case is probably a bug. ---AG
            v => return Err(self.errat(
                ReadError::InvalidAddValue { ty: Type::Float, val: v })),
        })
    }

    fn read_tag(&mut self, first: u8) -> CborResult<Cbor> {
        let tag = try!(self.read_uint(first));
        let tag = try!(tag.to_u64().map_err(|err| self.errat(err)));
        let data = try!(self.read_data_item(None));
        Ok(Cbor::Tag { tag: tag, data: Box::new(data) })
    }

    fn read_map(&mut self, first: u8) -> CborResult<Cbor> {
        let len = try!(self.read_len(first));
        let mut map = HashMap::with_capacity(len);
        for _ in 0..len {
            let key = match try!(self.read_data_item(None)) {
                Cbor::Unicode(s) => s,
                v => return Err(self.errat(
                    ReadError::mismatch(Type::Unicode, &v))),
            };
            let val = try!(self.read_data_item(None));
            map.insert(key, val);
        }
        Ok(Cbor::Map(map))
    }

    fn read_array(&mut self, first: u8) -> CborResult<Cbor> {
        let len = try!(self.read_len(first));
        let mut array = Vec::with_capacity(len);
        for _ in 0..len {
            let v = try!(self.read_data_item(None));
            array.push(v);
        }
        Ok(Cbor::Array(array))
    }

    fn read_string(&mut self, first: u8) -> CborResult<Cbor> {
        let len = try!(self.read_len(first));
        let mut buf = vec_from_elem(len, 0u8);
        try!(self.rdr.read_full(&mut buf));
        String::from_utf8(buf)
               .map(Cbor::Unicode)
               .map_err(|err| self.errstr(err.utf8_error().to_string()))
    }

    fn read_bytes(&mut self, first: u8) -> CborResult<Cbor> {
        let len = try!(self.read_len(first));
        let mut buf = vec_from_elem(len, 0u8);
        try!(self.rdr.read_full(&mut buf));
        Ok(Cbor::Bytes(buf))
    }

    fn read_len(&mut self, first: u8) -> CborResult<usize> {
        self.read_uint(first)
            .and_then(|v| v.to_usize().map_err(|err| self.errat(err)))
    }

    fn read_uint(&mut self, first: u8) -> CborResult<CborUnsigned> {
        Ok(match first & 0b000_11111 {
            n @ 0...23 => CborUnsigned::UInt8(n),
            24 => CborUnsigned::UInt8(try!(self.rdr.read_byte())),
            25 => CborUnsigned::UInt16(try!(self.rdr.read_u16::<BigEndian>())),
            26 => CborUnsigned::UInt32(try!(self.rdr.read_u32::<BigEndian>())),
            27 => CborUnsigned::UInt64(try!(self.rdr.read_u64::<BigEndian>())),
            v => return Err(self.errat(
                ReadError::InvalidAddValue { ty: Type::UInt, val: v })),
        })
    }

    fn read_int(&mut self, first: u8) -> CborResult<CborSigned> {
        Ok(match first & 0b000_11111 {
            n @ 0...23 => CborSigned::Int8(-1 - (n as i8)),
            24 => {
                let n = try!(self.rdr.read_byte());
                if n > ::std::i8::MAX as u8 {
                    CborSigned::Int16(-1 - (n as i16))
                } else {
                    CborSigned::Int8(-1 - (n as i8))
                }
            }
            25 => {
                let n = try!(self.rdr.read_u16::<BigEndian>());
                if n > ::std::i16::MAX as u16 {
                    CborSigned::Int32(-1 - (n as i32))
                } else {
                    CborSigned::Int16(-1 - (n as i16))
                }
            }
            26 => {
                let n = try!(self.rdr.read_u32::<BigEndian>());
                if n > ::std::i32::MAX as u32 {
                    CborSigned::Int64(-1 - (n as i64))
                } else {
                    CborSigned::Int32(-1 - (n as i32))
                }
            }
            27 => {
                let n = try!(self.rdr.read_u64::<BigEndian>());
                if n > ::std::i64::MAX as u64 {
                    return Err(self.errstr(format!(
                        "Negative integer out of range: {:?}", n)));
                }
                CborSigned::Int64(-1 - (n as i64))
            }
            v => return Err(self.errat(
                ReadError::InvalidAddValue { ty: Type::Int, val: v })),
        })
    }
}

struct CborReader<R> {
    rdr: R,
    // used for error reporting
    last_offset: usize,
    bytes_read: usize,
}

impl<R: IoReader> IoReader for CborReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> IoResult<usize> {
        let n = try!(self.rdr.read(buf));
        self.last_offset = self.bytes_read;
        self.bytes_read += n;
        Ok(n)
    }
}

impl<R: IoReader> CborReader<R> {
    fn new(rdr: R) -> CborReader<R> {
        CborReader { rdr: rdr, last_offset: 0, bytes_read: 0 }
    }

    fn read_full(&mut self, buf: &mut [u8]) -> IoResult<()> {
        let mut n = 0us;
        while n < buf.len() {
            n += try!(self.read(&mut buf[n..]));
        }
        Ok(())
    }
}

fn vec_from_elem<T: Copy>(len: usize, v: T) -> Vec<T> {
    let mut xs = Vec::with_capacity(len);
    unsafe { xs.set_len(len); }
    for x in &mut xs { *x = v; }
    xs
}
