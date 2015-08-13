use std::io::{self, Read};

use byteorder::{ReadBytesExt, BigEndian};
use rustc_serialize::Decoder as RustcDecoder;
use serde::{self, Deserialize};
use serde::de;

use {Type, CborResult, CborError, ReadError};

/// Experimental and incomplete direct decoder.
///
/// A "direct" decoder is one that does not use an intermediate abstact syntax
/// representation. Namely, the bytes are decoded directly into types. This
/// *significantly* impacts performance. For example, it doesn't have to box
/// and unbox every data item.
///
/// However, implementing a direct decoder is much harder in the existing
/// serialization infrastructure. Currently, structs and enums are not
/// implemented. (But `Vec`s, tuples, `Option`s and maps should work.)
pub struct Deserializer<R> {
    rdr: CborReader<R>,
    first: Option<u8>,
}

impl<R: io::Read> Deserializer<R> {
    /// Create a new CBOR deserializer from the underlying reader.
    pub fn from_reader(rdr: R) -> Deserializer<io::BufReader<R>> {
        Deserializer {
            rdr: CborReader::new(io::BufReader::new(rdr)),
            first: None,
        }
    }
}

impl Deserializer<io::Cursor<Vec<u8>>> {
    /// Create a new CBOR decoder that reads from the buffer given.
    ///
    /// The buffer is usually given as either a `Vec<u8>` or a `&[u8]`.
    pub fn from_bytes<'a, T>(bytes: T) -> Deserializer<io::Cursor<Vec<u8>>>
            where T: Into<Vec<u8>> {
        Deserializer {
            rdr: CborReader::new(io::Cursor::new(bytes.into())),
            first: None,
        }
    }
}


impl<R: io::Read> Deserializer<R> {
    fn errat(&self, err: ReadError) -> CborError {
        CborError::AtOffset { kind: err, offset: self.rdr.last_offset }
    }

    fn errstr(&self, s: String) -> CborError {
        self.errat(ReadError::Other(s))
    }

    fn err(&self, err: ReadError) -> CborError {
        CborError::Decode(err)
    }

    fn miss(&self, expected: Type, got: u8) -> CborError {
        self.err(ReadError::miss(expected, got))
    }

    fn peek_marker(&mut self) -> CborResult<u8> {
        match self.first {
            Some(value) => Ok(value),
            None => {
                let first = try!(self.rdr.read_u8());
                self.first = Some(first);
                Ok(first)
            }
        }
    }

    fn read_marker(&mut self) -> CborResult<u8> {
        match self.first.take() {
            Some(value) => Ok(value),
            None => Ok(try!(self.rdr.read_u8())),
        }
    }

    fn read_value<V>(&mut self, first: u8, visitor: V) -> CborResult<V::Value>
        where V: serde::de::Visitor,
    {
        match (first & 0b111_00000) >> 5 {
            0 => self.read_usize(first, visitor),
            1 => self.read_isize(first, visitor),
            2 => self.read_bytes(first, visitor),
            3 => self.read_string(first, visitor),
            4 => self.read_array(first, visitor),
            5 => self.read_map(first, visitor),
            6 => self.read_tag(first, visitor),
            7 => match first & 0b000_11111 {
                v @ 0...23 => self.read_simple_value(v, visitor),
                24 => {
                    let b = try!(self.rdr.read_u8());
                    self.read_simple_value(b, visitor)
                }
                25...27 => self.read_float(first, visitor),
                v @ 28...30 =>
                    Err(self.errat(
                        ReadError::Unassigned { major: 7, add: v })),
                //31 => Ok(Cbor::Break),
                // Because max(byte & 0b000_11111) == 2^5 - 1 == 31
                _ => {
                    unreachable!("bah2 {} {} {}", first, (first & 0b111_00000) >> 5, first & 0b000_11111);
                    //unreachable!()
                }
            },
            // This is truly unreachable because `byte & 0b111_00000 >> 5`
            // can only produce 8 distinct values---each of which are handled
            // above. ---AG
            _ => {
                unreachable!("bah! {} {}", first, (first & 0b111_00000) >> 5);
                //unreachable!()
            }
        }
    }

    fn read_len(&mut self, first: u8) -> CborResult<usize> {
        self.read_usize(first, serde::de::impls::PrimitiveVisitor::new())
    }

    fn read_type(&mut self, first: u8, expected: Type) -> CborResult<u8> {
        if (first & 0b111_00000) >> 5 == expected.major() {
            Ok(first)
        } else {
            Err(self.miss(expected, first))
        }
    }

    fn read_simple_value<V>(&mut self, val: u8, mut visitor: V) -> CborResult<V::Value>
        where V: serde::de::Visitor,
    {
        match val {
            v @ 0...19 =>
                Err(self.errat(
                    ReadError::Unassigned { major: 7, add: v })),
            20 => visitor.visit_bool(false),
            21 => visitor.visit_bool(true),
            22 => visitor.visit_unit(),
            23 => panic!("unimplemented"),
            //23 => Cbor::Undefined,
            v @ 24...31 =>
                Err(self.errat(
                    ReadError::Reserved { major: 7, add: v })),
            v /* 32...255 */ =>
                Err(self.errat(
                    ReadError::Unassigned { major: 7, add: v })),
        }
    }

    fn read_float<V>(&mut self, first: u8, mut visitor: V) -> CborResult<V::Value>
        where V: serde::de::Visitor,
    {
        match ((first & 0b111_00000) >> 5, first & 0b000_11111) {
            (0, n) => {
                self.read_usize(n, visitor)
            }
            (1, n) => {
                self.read_isize(n, visitor)
            }
            (7, 25) => {
                // Rust doesn't have a `f16` type, so just read a u16 and
                // cast it to a f64. I think this is wrong. ---AG
                visitor.visit_f64(try!(self.rdr.read_u16::<BigEndian>()) as f64)
            }
            (7, 26) => {
                visitor.visit_f32(try!(self.rdr.read_f32::<BigEndian>()))
            }
            (7, 27) => {
                visitor.visit_f64(try!(self.rdr.read_f64::<BigEndian>()))
            }
            _ => Err(self.miss(Type::Float, first)),
        }
    }

    fn read_isize<V>(&mut self, first: u8, mut visitor: V) -> CborResult<V::Value>
        where V: serde::de::Visitor,
    {
        match first & 0b000_11111 {
            n @ 0...23 => visitor.visit_i8(-1 - (n as i8)),
            24 => {
                let n = try!(self.rdr.read_u8());
                if n > ::std::i8::MAX as u8 {
                    visitor.visit_i16(-1 - (n as i16))
                } else {
                    visitor.visit_i8(-1 - (n as i8))
                }
            }
            25 => {
                let n = try!(self.rdr.read_u16::<BigEndian>());
                if n > ::std::i16::MAX as u16 {
                    visitor.visit_i32(-1 - (n as i32))
                } else {
                    visitor.visit_i16(-1 - (n as i16))
                }
            }
            26 => {
                let n = try!(self.rdr.read_u32::<BigEndian>());
                if n > ::std::i32::MAX as u32 {
                    visitor.visit_i64(-1 - (n as i64))
                } else {
                    visitor.visit_i32(-1 - (n as i32))
                }
            }
            27 => {
                let n = try!(self.rdr.read_u64::<BigEndian>());
                if n > ::std::i64::MAX as u64 {
                    return Err(self.errstr(format!(
                        "Negative integer out of range: {:?}", n)));
                }
                visitor.visit_i64(-1 - (n as i64))
            }
            v => Err(self.errat(
                ReadError::InvalidAddValue { ty: Type::Int, val: v })),
        }
    }

    fn read_usize<V>(&mut self, first: u8, mut visitor: V) -> CborResult<V::Value>
        where V: serde::de::Visitor,
    {
        match first & 0b000_11111 {
            n @ 0...23 => visitor.visit_u8(n),
            24 => visitor.visit_u8(try!(self.rdr.read_u8())),
            25 => visitor.visit_u16(try!(self.rdr.read_u16::<BigEndian>())),
            26 => visitor.visit_u32(try!(self.rdr.read_u32::<BigEndian>())),
            27 => visitor.visit_u64(try!(self.rdr.read_u64::<BigEndian>())),
            v => Err(self.errat(
                ReadError::InvalidAddValue { ty: Type::UInt, val: v })),
        }
    }

    fn read_tag<V>(&mut self, first: u8, visitor: V) -> CborResult<V::Value>
        where V: serde::de::Visitor,
    {
        self.read_usize(first, visitor)
    }

    fn read_map<V>(&mut self, first: u8, mut visitor: V) -> CborResult<V::Value>
        where V: serde::de::Visitor,
    {
        let len = try!(self.read_len(first));
        visitor.visit_map(MapVisitor {
            deserializer: self,
            len: len,
        })
    }

    fn read_array<V>(&mut self, first: u8, mut visitor: V) -> CborResult<V::Value>
        where V: serde::de::Visitor,
    {
        let len = try!(self.read_len(first));
        visitor.visit_seq(SeqVisitor {
            deserializer: self,
            len: len,
        })
    }

    fn read_string<V>(&mut self, first: u8, mut visitor: V) -> CborResult<V::Value>
        where V: serde::de::Visitor,
    {
        let b = try!(self.read_type(first, Type::Unicode));
        let len = try!(self.read_len(b));
        let mut buf = vec_from_elem(len, 0);
        try!(self.rdr.read_full(&mut buf));

        let string = match String::from_utf8(buf) {
            Ok(string) => string,
            Err(err) => { return Err(self.errstr(err.utf8_error().to_string())); }
        };

        visitor.visit_string(string)
    }

    fn read_bytes<V>(&mut self, first: u8, mut visitor: V) -> CborResult<V::Value>
        where V: serde::de::Visitor,
    {
        let len = try!(self.read_len(first));
        let mut buf = vec_from_elem(len, 0);
        try!(self.rdr.read_full(&mut buf));
        visitor.visit_byte_buf(buf)
    }
}

struct SeqVisitor<'a, R: 'a> {
    deserializer: &'a mut Deserializer<R>,
    len: usize,
}

impl<'a, R> serde::de::SeqVisitor for SeqVisitor<'a, R>
    where R: io::Read,
{
    type Error = CborError;

    fn visit<T>(&mut self) -> CborResult<Option<T>>
        where T: serde::Deserialize,
    {
        if self.len == 0 {
            Ok(None)
        } else {
            self.len -= 1;
            Ok(Some(try!(Deserialize::deserialize(self.deserializer))))
        }
    }

    fn end(&mut self) -> CborResult<()> {
        if self.len == 0 {
            Ok(())
        } else {
            Err(self.deserializer.errstr("Unexpected end of array".to_string()))
        }
    }
}

struct MapVisitor<'a, R: 'a> {
    deserializer: &'a mut Deserializer<R>,
    len: usize,
}

impl<'a, R> serde::de::MapVisitor for MapVisitor<'a, R>
    where R: io::Read,
{
    type Error = CborError;

    fn visit_key<T>(&mut self) -> CborResult<Option<T>>
        where T: serde::Deserialize,
    {
        if self.len == 0 {
            Ok(None)
        } else {
            self.len -= 1;
            // FIXME: make sure field is unicode
            Ok(Some(try!(Deserialize::deserialize(self.deserializer))))
        }
    }

    fn visit_value<T>(&mut self) -> CborResult<T>
        where T: serde::Deserialize,
    {
        Ok(try!(Deserialize::deserialize(self.deserializer)))
    }

    fn end(&mut self) -> CborResult<()> {
        if self.len == 0 {
            Ok(())
        } else {
            Err(self.deserializer.errstr("Unexpected end of array".to_string()))
        }
    }
}

impl<R> serde::Deserializer for Deserializer<R>
    where R: io::Read,
{
    type Error = CborError;

    fn visit<V>(&mut self, visitor: V) -> CborResult<V::Value>
        where V: serde::de::Visitor,
    {
        let first = try!(self.read_marker());
        self.read_value(first, visitor)
    }

    fn visit_struct<V>(&mut self,
                       name: &str,
                       _fields: &[&str],
                       visitor: V) -> CborResult<V::Value>
        where V: serde::de::Visitor,
    {
        match name {
            "CborTag" => {
                let first = try!(self.read_marker());
                match (first & 0b111_00000) >> 5 {
                    //6 => self.read_tag(first, visitor),
                    _ => panic!("visit_named_enum")
                }
            }
            _ => self.visit(visitor),
        }
    }

    fn visit_enum<V>(&mut self,
                     _name: &str,
                     _variants: &[&str],
                     mut visitor: V) -> CborResult<V::Value>
        where V: serde::de::EnumVisitor,
    {
        let first = try!(self.peek_marker());

        match (first & 0b111_00000) >> 5 {
            3 => {
                visitor.visit(StringVariantVisitor {
                    de: self,
                })
            }
            5 => {
                self.first = None;

                let len = try!(self.read_len(first));
                if len != 1 {
                    return Err(self.errstr(String::from("Too many fields in variant map")));
                }

                visitor.visit(self)
            }
            _ => {
                return Err(self.errstr(String::from("Expected variant map")));
            }
        }
    }
}

struct StringVariantVisitor<'a, R: io::Read + 'a> {
    de: &'a mut Deserializer<R>,
}

impl<'a, R: io::Read> de::VariantVisitor for StringVariantVisitor<'a, R> {
    type Error = CborError;

    fn visit_variant<V>(&mut self) -> CborResult<V>
        where V: de::Deserialize
    {
        de::Deserialize::deserialize(self.de)
    }

    fn visit_unit(&mut self) -> CborResult<()> {
        Ok(())
    }
}

impl<R: io::Read> de::VariantVisitor for Deserializer<R> {
    type Error = CborError;

    fn visit_variant<V>(&mut self) -> CborResult<V>
        where V: de::Deserialize
    {
        de::Deserialize::deserialize(self)
    }

    fn visit_unit(&mut self) -> CborResult<()> {
        de::Deserialize::deserialize(self)
    }

    fn visit_newtype<T>(&mut self) -> CborResult<T>
        where T: de::Deserialize,
    {
        de::Deserialize::deserialize(self)
    }

    fn visit_tuple<V>(&mut self,
                      _len: usize,
                      visitor: V) -> CborResult<V::Value>
        where V: de::Visitor,
    {
        de::Deserializer::visit(self, visitor)
    }

    fn visit_struct<V>(&mut self,
                       _fields: &'static [&'static str],
                       visitor: V) -> CborResult<V::Value>
        where V: de::Visitor,
    {
        de::Deserializer::visit(self, visitor)
    }
}

/// A very light layer over a basic reader that keeps track of offset
/// information at the byte level.
struct CborReader<R> {
    rdr: R,
    // read from here before going back to rdr
    buf: Vec<u8>,
    // used for error reporting
    last_offset: usize,
    bytes_read: usize,
}

impl<R: io::Read> io::Read for CborReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        if !self.buf.is_empty() {
            if self.buf.len() <= buf.len() {
                let nread = self.buf.len();
                for (i, &x) in self.buf.iter().enumerate() {
                    buf[i] = x;
                }
                self.buf.truncate(0);
                Ok(nread)
            } else {
                for (i, x) in buf.iter_mut().enumerate() {
                    *x = self.buf[i];
                }
                for (i0, i1) in (0..).zip(buf.len()..self.buf.len()) {
                    self.buf[i0] = self.buf[i1];
                }
                let new_len = self.buf.len() - buf.len();
                self.buf.truncate(new_len);
                Ok(buf.len())
            }
        } else {
            let n = try!(self.rdr.read(buf));
            self.last_offset = self.bytes_read;
            self.bytes_read += n;
            Ok(n)
        }
    }
}

impl<R: io::Read> CborReader<R> {
    fn new(rdr: R) -> CborReader<R> {
        CborReader {
            rdr: rdr,
            buf: Vec::with_capacity(1 << 16),
            last_offset: 0,
            bytes_read: 0,
        }
    }

    fn read_full(&mut self, buf: &mut [u8]) -> CborResult<()> {
        let mut n = 0usize;
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
