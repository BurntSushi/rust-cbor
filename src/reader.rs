use std::borrow::{IntoCow, ToOwned};
use std::old_io::{IoError, IoResult, MemReader};
use std::old_io::Reader as IoReader;

use byteorder::{ReaderBytesExt, BigEndian};
use rustc_serialize::Decodable;

use {
    Cbor, CborUnsigned, CborSigned,
    Type,
    CborResult, CborError, ReadError,
    CborDecodable, CborDecoder,
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
        CborDecodable::cbor_decode(&mut CborDecoder::new(v))
    }

    pub fn rustc_decode<D>(&mut self) -> CborResult<D> where D: Decodable {
        Decodable::decode(&mut CborDecoder::new(try!(self.read())))
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
            _ => unreachable!(),
        }
    }

    fn read_array(&mut self, first: u8) -> CborResult<Cbor> {
        let len = try!(self.read_len(first));
        let mut array = Vec::with_capacity(len);
        for _ in 0..len {
            array.push(try!(self.read_data_item(None)));
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
            24 => CborSigned::Int8(-1 - (try!(self.rdr.read_byte()) as i8)),
            25 => CborSigned::Int16(
                -1 - try!(self.rdr.read_i16::<BigEndian>())),
            26 => CborSigned::Int32(
                -1 - try!(self.rdr.read_i32::<BigEndian>())),
            27 => CborSigned::Int64(
                -1 - try!(self.rdr.read_i64::<BigEndian>())),
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
