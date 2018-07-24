use std::cmp;
use std::convert::Into;
use std::collections::hash_map::HashMap;
use std::io::{self, Read};
use std::mem::transmute;

use byteorder::{ReadBytesExt, BigEndian};
use rustc_serialize::Decodable;

use rustc_decoder::CborDecoder;
use {
    Cbor, CborUnsigned, CborSigned, CborFloat, CborBytes, CborTag, Type,
    CborResult, CborError, ReadError,
};

/// Read CBOR data items into Rust values from the underlying reader `R`.
pub struct Decoder<R> {
    rdr: CborReader<R>,
}

impl<R: io::Read> Decoder<R> {
    /// Create a new CBOR decoder from the underlying reader.
    pub fn from_reader(rdr: R) -> Decoder<io::BufReader<R>> {
        Decoder { rdr: CborReader::new(io::BufReader::new(rdr)) }
    }
}

fn is_indefinite(first: u8) -> bool {
    (first & 0b000_11111) == 0b000_11111
}

impl<R: io::Read> Decoder<R> {
    /// Decode a sequence of top-level CBOR data items into Rust values.
    ///
    /// # Example
    ///
    /// This shows how to encode and decode a sequence of data items:
    ///
    /// ```rust
    /// use cbor::{Decoder, Encoder};
    ///
    /// let data = vec![("a".to_string(), 1), ("b".to_string(), 2),
    ///                 ("c".to_string(), 3)];
    ///
    /// let mut enc = Encoder::from_memory();
    /// enc.encode(&data).unwrap();
    ///
    /// let mut dec = Decoder::from_bytes(enc.as_bytes());
    /// let items: Vec<(String, i32)> = dec.decode()
    ///                                    .collect::<Result<_, _>>()
    ///                                    .unwrap();
    ///
    /// assert_eq!(items, data);
    /// ```
    pub fn decode<D: Decodable>(&mut self) -> DecodedItems<R, D> {
        DecodedItems {
            it: self.items(),
            _phantom: ::std::marker::PhantomData,
        }
    }

    /// Read a sequence of top-level CBOR data items.
    ///
    /// This yields data items represented by the `Cbor` type, which is its
    /// abstract syntax. (Using the `decode` iterator is probably much more
    /// convenient, but this is useful when you need to do more sophisticated
    /// analysis on the CBOR data.)
    ///
    /// # Example
    ///
    /// This shows how to encode and decode a sequence of data items:
    ///
    /// ```rust
    /// use cbor::{Cbor, CborUnsigned, Decoder, Encoder};
    ///
    /// let mut enc = Encoder::from_memory();
    /// enc.encode(vec![("a", 1), ("b", 2), ("c", 3)]).unwrap();
    ///
    /// let mut dec = Decoder::from_bytes(enc.as_bytes());
    /// let items = dec.items().collect::<Result<Vec<_>, _>>().unwrap();
    ///
    /// assert_eq!(items, vec![
    ///     Cbor::Array(vec![
    ///         Cbor::Unicode("a".to_string()),
    ///         Cbor::Unsigned(CborUnsigned::UInt8(1)),
    ///     ]),
    ///     Cbor::Array(vec![
    ///         Cbor::Unicode("b".to_string()),
    ///         Cbor::Unsigned(CborUnsigned::UInt8(2)),
    ///     ]),
    ///     Cbor::Array(vec![
    ///         Cbor::Unicode("c".to_string()),
    ///         Cbor::Unsigned(CborUnsigned::UInt8(3)),
    ///     ]),
    /// ]);
    /// ```
    pub fn items(&mut self) -> Items<R> {
        Items { dec: self }
    }

    fn read_data_item(&mut self, first: Option<u8>) -> CborResult<Cbor> {
        let first = match first {
            Some(first) => first,
            None => try!(self.rdr.read_u8()),
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
                    let b = try!(self.rdr.read_u8());
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
                // I think this is wrong. ---AG
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
        let tag = self.read_uint(first)?;
        let tag = try!(tag.to_u64().map_err(|err| self.errat(err)));
        let data = try!(self.read_data_item(None));
        Ok(Cbor::Tag(CborTag { tag: tag, data: Box::new(data) }))
    }

    fn read_map_key(&mut self, first: Option<u8>) -> CborResult<String> {
        let at = self.rdr.bytes_read; // for coherent error reporting
        match self.read_data_item(first)? {
            Cbor::Unicode(s) => Ok(s),
            Cbor::Bytes(CborBytes(bytes)) => {
                match String::from_utf8(bytes) {
                    Ok(s) => Ok(s),
                    Err(err) => return Err(CborError::AtOffset {
                        kind: ReadError::Other(err.to_string()),
                        offset: at,
                    }),
                }
            }
            v => return Err(CborError::AtOffset {
                kind: ReadError::mismatch(Type::Unicode, &v),
                offset: at,
            }),
        }
    }

    fn read_map(&mut self, first: u8) -> CborResult<Cbor> {

        let mut map: HashMap<String,Cbor>;

        if is_indefinite(first) {
            map = HashMap::new();
            loop {
                let first = self.rdr.read_u8()?;
                if 0xff == first {
                    break;
                }
                let key = self.read_map_key(Some(first))?;
                let val = self.read_data_item(None)?;
                map.insert(key, val);
            }
        }else {
            let len = try!(self.read_len(first));
            map = HashMap::with_capacity(len);
            for _ in 0..len {
                let key = self.read_map_key(None)?;
                let val = try!(self.read_data_item(None));
                map.insert(key, val);
            }
        }
        Ok(Cbor::Map(map))
    }

    fn read_array(&mut self, first: u8) -> CborResult<Cbor> {
        let mut array: Vec<Cbor>;

        if is_indefinite(first) {
            array = vec![];
            loop {
                let v = self.read_data_item(None)?;
                if Cbor::Break == v {
                    break
                }
                array.push(v)
            }
        } else {
            let len = self.read_len(first)?;
            array = Vec::with_capacity(cmp::min(100000, len));
            for _ in 0..len {
                let v = self.read_data_item(None)?;
                array.push(v);
            }
        }

        Ok(Cbor::Array(array))
    }

    fn read_string(&mut self, first: u8) -> CborResult<Cbor> {

        // Indefinite length, consume chunks until "break"
        if is_indefinite(first) {
            let mut chunks: Vec<String> = vec![];

            loop {
                let at = self.rdr.bytes_read; // for coherent error reporting
                match self.read_data_item(None)? {
                    Cbor::Unicode(u) => chunks.push(u),
                    Cbor::Break => return Ok(Cbor::Unicode(chunks.concat())),
                    other => return Err(CborError::AtOffset {
                        kind: ReadError::mismatch(Type::Unicode, &other),
                        offset: at
                    })
                }
            }

        } else {
            let len = try!(self.read_len(first));
            let mut buf: Vec<u8> = vec_from_elem(len, 0u8);
            try!(self.rdr.read_full(&mut buf));

            String::from_utf8(buf)
                .map(Cbor::Unicode)
                .map_err(|err| self.errstr(err.utf8_error().to_string()))
        }
    }

    fn read_bytes(&mut self, first: u8) -> CborResult<Cbor> {
        if is_indefinite(first) {
            let mut chunks: Vec<Vec<u8>> = vec![];

            loop {
                let at = self.rdr.bytes_read; // for coherent error reporting
                match self.read_data_item(None)? {
                    Cbor::Bytes(b) => chunks.push(b.to_vec()),
                    Cbor::Break => return Ok(Cbor::Bytes(CborBytes(chunks.concat()))),
                    other => return Err(CborError::AtOffset {
                        kind: ReadError::mismatch(Type::Bytes, &other),
                        offset: at,
                    })
                }
            }
        } else {
            let len = try!(self.read_len(first));
            let mut buf = vec_from_elem(len, 0u8);
            try!(self.rdr.read_full(&mut buf));
            Ok(Cbor::Bytes(CborBytes(buf)))
        }
    }

    fn read_len(&mut self, first: u8) -> CborResult<usize> {
        self.read_uint(first)
            .and_then(|v| v.to_usize().map_err(|err| self.errat(err)))
    }

    fn read_uint(&mut self, first: u8) -> CborResult<CborUnsigned> {
        Ok(match first & 0b000_11111 {
            n @ 0...23 => CborUnsigned::UInt8(n),
            24 => CborUnsigned::UInt8(try!(self.rdr.read_u8())),
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
                let n = try!(self.rdr.read_u8());
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

impl Decoder<io::Cursor<Vec<u8>>> {
    /// Create a new CBOR decoder that reads from the buffer given.
    ///
    /// The buffer is usually given as either a `Vec<u8>` or a `&[u8]`.
    pub fn from_bytes<T>(bytes: T) -> Decoder<io::Cursor<Vec<u8>>>
            where T: Into<Vec<u8>> {
        Decoder { rdr: CborReader::new(io::Cursor::new(bytes.into())) }
    }
}

impl<R: io::Read> Decoder<R> {
    fn errat(&self, err: ReadError) -> CborError {
        CborError::AtOffset { kind: err, offset: self.rdr.last_offset }
    }

    fn errstr(&self, s: String) -> CborError {
        self.errat(ReadError::Other(s))
    }
}

/// An iterator over items decoded from CBOR into Rust values.
///
/// `D` represents the type of the Rust value being decoded into, `R`
/// represents the underlying reader and `'a` is the lifetime of the decoder.
pub struct DecodedItems<'a, R: 'a, D> {
    it: Items<'a, R>,
    _phantom: ::std::marker::PhantomData<D>,
}

impl<'a, R: io::Read, D: Decodable> Iterator for DecodedItems<'a, R, D> {
    type Item = CborResult<D>;

    fn next(&mut self) -> Option<CborResult<D>> {
        self.it.next().map(|result| {
            result.and_then(|v| Decodable::decode(&mut CborDecoder::new(v)))
        })
    }
}

/// An iterator over CBOR items in terms of the abstract syntax.
///
/// `R` represents the underlying reader and `'a` is the lifetime of the
/// decoder.
pub struct Items<'a, R: 'a> {
    dec: &'a mut Decoder<R>,
}

impl<'a, R: io::Read> Iterator for Items<'a, R> {
    type Item = CborResult<Cbor>;

    fn next(&mut self) -> Option<CborResult<Cbor>> {
        let first = match self.dec.rdr.read_u8().map_err(CborError::from) {
            Ok(v) => v,
            Err(ref err) if err.is_eof() => return None,
            Err(err) => return Some(Err(err)),
        };
        Some(self.dec.read_data_item(Some(first)))
    }
}

/// A very light layer over a basic reader that keeps track of offset
/// information at the byte level.
struct CborReader<R> {
    rdr: R,
    // used for error reporting
    last_offset: usize,
    bytes_read: usize,
}

impl<R: io::Read> io::Read for CborReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let n = try!(self.rdr.read(buf));
        self.last_offset = self.bytes_read;
        self.bytes_read += n;
        Ok(n)
    }
}

impl<R: io::Read> CborReader<R> {
    fn new(rdr: R) -> CborReader<R> {
        CborReader {
            rdr: rdr,
            last_offset: 0,
            bytes_read: 0,
        }
    }

    fn read_full(&mut self, buf: &mut [u8]) -> CborResult<()> {
        let mut nread = 0usize;
        while nread < buf.len() {
            match try!(self.read(&mut buf[nread..])) {
                0 => return Err(CborError::UnexpectedEOF),
                n => nread += n,
            }
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
