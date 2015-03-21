use std::borrow::{IntoCow, ToOwned};
use std::char;
use std::io::{self, Read};

use byteorder::{ReadBytesExt, BigEndian};
use rustc_serialize::Decoder as RustcDecoder;

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
pub struct CborDecoder<R> {
    rdr: CborReader<R>,
}

impl CborDecoder<io::Cursor<Vec<u8>>> {
    /// Create a new CBOR decoder that reads from the buffer given.
    ///
    /// The buffer is usually given as either a `Vec<u8>` or a `&[u8]`.
    pub fn from_bytes<'a, T>(bytes: T) -> CborDecoder<io::Cursor<Vec<u8>>>
            where T: IntoCow<'a, [u8]> {
        let rdr = io::Cursor::new(bytes.into_cow().into_owned());
        CborDecoder { rdr: CborReader::new(rdr) }
    }
}

impl<R: io::Read> CborDecoder<io::BufReader<R>> {
    /// Create a new CBOR decoder that reads from the reader given.
    pub fn from_reader(rdr: R) -> CborDecoder<io::BufReader<R>> {
        CborDecoder { rdr: CborReader::new(io::BufReader::new(rdr)) }
    }
}

impl<R: io::Read> CborDecoder<R> {
    fn err(&self, err: ReadError) -> CborError {
        CborError::Decode(err)
    }

    fn errstr(&self, s: String) -> CborError {
        self.err(ReadError::Other(s))
    }

    fn miss(&self, expected: Type, got: u8) -> CborError {
        self.err(ReadError::miss(expected, got))
    }

    fn read_len(&mut self, first: Option<u8>) -> CborResult<usize> {
        // TODO: Should really check for overflow here... ---AG
        self.read_uint(first.map(|n| n & 0b000_11111), 64).map(|n| n as usize)
    }

    fn read_type(&mut self, expected: Type)
                -> CborResult<u8> {
        let b = try!(self.rdr.read_u8());
        if (b & 0b111_00000) >> 5 == expected.major() {
            Ok(b)
        } else {
            Err(self.miss(expected, b))
        }
    }

    fn read_float(&mut self, first: Option<u8>, expect_size: u8)
                 -> CborResult<f64> {
        let b = match first {
            Some(b) => b,
            None => try!(self.rdr.read_u8()),
        };
        let (n, size) = match ((b & 0b111_00000) >> 5, b & 0b000_11111) {
            (0, n) => {
                return self.read_uint(Some(n), expect_size).map(|n| n as f64);
            }
            (1, n) => {
                return self.read_int(Some(n), expect_size).map(|n| n as f64);
            }
            (7, 25) => {
                // Rust doesn't have a `f16` type, so just read a u16 and
                // cast it to a f64. I think this is wrong. ---AG
                (try!(self.rdr.read_u16::<BigEndian>()) as f64, 16)
            }
            (7, 26) => (try!(self.rdr.read_f32::<BigEndian>()) as f64, 32),
            (7, 27) => (try!(self.rdr.read_f64::<BigEndian>()), 64),
            _ => return Err(self.miss(Type::Float, b)),
        };
        if size > expect_size {
            Err(self.errstr(format!(
                "Expected floating point number ({} bits or fewer), but got \
                 {} bit floating point number: {}.", expect_size, size, n)))
        } else {
            Ok(n)
        }
    }

    fn read_int(&mut self, first: Option<u8>, expect_size: u8)
                -> CborResult<i64> {
        let b = match first {
            Some(b) => b,
            None => try!(self.rdr.read_u8()),
        };
        let n = match ((b & 0b111_00000) >> 5, b & 0b000_11111) {
            (0, n) => {
                return self.read_uint(Some(n), expect_size).map(|n| n as i64);
            }
            (1, n @ 0...23) => n as i64,
            (1, 24) => try!(self.rdr.read_u8()) as i64,
            (1, 25) => try!(self.rdr.read_i16::<BigEndian>()) as i64,
            (1, 26) => try!(self.rdr.read_i32::<BigEndian>()) as i64,
            (1, 27) => try!(self.rdr.read_i64::<BigEndian>()),
            _ => return Err(self.miss(Type::Int, b)),
        };

        fn size(n: i64) -> u8 {
            if n <= ::std::i8::MAX as i64 {
                8
            } else if n <= ::std::i16::MAX as i64 {
                16
            } else if n <= ::std::i32::MAX as i64 {
                32
            } else {
                64
            }
        }

        let n_size = size(n);
        if n_size > expect_size {
            Err(self.errstr(format!(
                "Expected negative integer ({} bits or fewer), but got \
                 {} bit number: {}.", expect_size, n_size, -1 - n)))
        } else {
            Ok(-1 - n)
        }
    }

    fn read_uint(&mut self, first: Option<u8>, expect_size: u8)
                -> CborResult<u64> {
        let b = match first {
            Some(b) => b,
            None => try!(self.rdr.read_u8()),
        };
        let (n, size) = match ((b & 0b111_00000) >> 5, b & 0b000_11111) {
            (0, n @ 0...23) => (n as u64, 8),
            (0, 24) => (try!(self.rdr.read_u8()) as u64, 8),
            (0, 25) => (try!(self.rdr.read_u16::<BigEndian>()) as u64, 16),
            (0, 26) => (try!(self.rdr.read_u32::<BigEndian>()) as u64, 32),
            (0, 27) => (try!(self.rdr.read_u64::<BigEndian>()), 64),
            _ => return Err(self.miss(Type::UInt, b)),
        };
        if size > expect_size {
            Err(self.errstr(format!(
                "Expected unsigned integer ({} bits or fewer), but got \
                 {} bit number: {}.", expect_size, size, n)))
        } else {
            Ok(n)
        }
    }
}

impl<R: io::Read> RustcDecoder for CborDecoder<R> {
    type Error = CborError;

    fn error(&mut self, err: &str) -> CborError {
        self.err(ReadError::Other(err.to_owned()))
    }

    fn read_nil(&mut self) -> CborResult<()> {
        let b = try!(self.rdr.read_u8());
        if (b & 0b111_00000) >> 5 == 7 && b & 0b000_11111 == 22 {
            Ok(())
        } else {
            Err(self.miss(Type::Null, b))
        }
    }

    fn read_usize(&mut self) -> CborResult<usize> {
        // Shouldn't this fail if we read a u64 but usize is only 32 bits?
        Ok(try!(self.read_uint(None, 64)) as usize)
    }

    fn read_u64(&mut self) -> CborResult<u64> {
        self.read_uint(None, 64)
    }

    fn read_u32(&mut self) -> CborResult<u32> {
        Ok(try!(self.read_uint(None, 32)) as u32)
    }

    fn read_u16(&mut self) -> CborResult<u16> {
        Ok(try!(self.read_uint(None, 16)) as u16)
    }

    fn read_u8(&mut self) -> CborResult<u8> {
        Ok(try!(self.read_uint(None, 8)) as u8)
    }

    fn read_isize(&mut self) -> CborResult<isize> {
        // Shouldn't this fail if we read a i64 but isize is only 32 bits?
        Ok(try!(self.read_int(None, 64)) as isize)
    }

    fn read_i64(&mut self) -> CborResult<i64> {
        self.read_int(None, 64)
    }

    fn read_i32(&mut self) -> CborResult<i32> {
        Ok(try!(self.read_int(None, 32)) as i32)
    }

    fn read_i16(&mut self) -> CborResult<i16> {
        Ok(try!(self.read_int(None, 16)) as i16)
    }

    fn read_i8(&mut self) -> CborResult<i8> {
        Ok(try!(self.read_int(None, 8)) as i8)
    }

    fn read_bool(&mut self) -> CborResult<bool> {
        let b = try!(self.rdr.read_u8());
        match ((b & 0b111_00000) >> 5, b & 0b000_11111) {
            (7, 20) => Ok(false),
            (7, 21) => Ok(true),
            _ => Err(self.miss(Type::Bool, b)),
        }
    }

    fn read_f64(&mut self) -> CborResult<f64> {
        self.read_float(None, 64)
    }

    fn read_f32(&mut self) -> CborResult<f32> {
        Ok(try!(self.read_float(None, 64)) as f32)
    }

    fn read_char(&mut self) -> CborResult<char> {
        let n = try!(self.read_uint(None, 32)) as u32;
        match char::from_u32(n) {
            Some(c) => Ok(c),
            None => Err(self.errstr(format!(
                "Could not convert '{:?}' to Unicode scalar value.", n))),
        }
    }

    fn read_str(&mut self) -> CborResult<String> {
        let b = try!(self.read_type(Type::Unicode));
        let len = try!(self.read_len(Some(b)));
        let mut buf = vec_from_elem(len, 0u8);
        try!(self.rdr.read_full(&mut buf));
        String::from_utf8(buf)
               .map_err(|err| self.errstr(err.utf8_error().to_string()))
    }

    fn read_enum<T, F>(&mut self, _name: &str, _f: F) -> CborResult<T>
            where F: FnOnce(&mut CborDecoder<R>) -> CborResult<T> {
        unreachable!()
    }

    fn read_enum_variant<T, F>(
        &mut self,
        _names: &[&str],
        mut _f: F,
    ) -> CborResult<T>
    where F: FnMut(&mut CborDecoder<R>, usize) -> CborResult<T> {
        unreachable!()
    }

    fn read_enum_variant_arg<T, F>(
        &mut self,
        _a_idx: usize,
        _f: F,
    ) -> CborResult<T>
    where F: FnOnce(&mut CborDecoder<R>) -> CborResult<T> {
        unreachable!()
    }

    fn read_enum_struct_variant<T, F>(
        &mut self,
        _names: &[&str],
        _f: F,
    ) -> CborResult<T>
    where F: FnMut(&mut CborDecoder<R>, usize) -> CborResult<T> {
        unreachable!()
    }

    fn read_enum_struct_variant_field<T, F>(
        &mut self,
        _f_name: &str,
        _f_idx: usize,
        _f: F,
    ) -> CborResult<T>
    where F: FnOnce(&mut CborDecoder<R>) -> CborResult<T> {
        unreachable!()
    }

    fn read_struct<T, F>(
        &mut self,
        _s_name: &str,
        _len: usize,
        _f: F,
    ) -> CborResult<T>
    where F: FnOnce(&mut CborDecoder<R>) -> CborResult<T> {
        unreachable!()
    }

    fn read_struct_field<T, F>(
        &mut self,
        _f_name: &str,
        _f_idx: usize,
        _f: F,
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
        let b = try!(self.read_type(Type::Array));
        let got_len = try!(self.read_len(Some(b)));
        if len != got_len {
            return Err(self.errstr(format!(
                "Expected tuple of length {:?}, but got array of length {:?}",
                len, got_len)));
        }
        f(self)
    }

    fn read_tuple_arg<T, F>(
        &mut self,
        _a_idx: usize,
        f: F,
    ) -> CborResult<T>
    where F: FnOnce(&mut CborDecoder<R>) -> CborResult<T> {
        f(self)
    }

    fn read_tuple_struct<T, F>(
        &mut self,
        _s_name: &str,
        len: usize,
        f: F,
    ) -> CborResult<T>
    where F: FnOnce(&mut CborDecoder<R>) -> CborResult<T> {
        self.read_tuple(len, f)
    }

    fn read_tuple_struct_arg<T, F>(
        &mut self,
        _a_idx: usize,
        f: F,
    ) -> CborResult<T>
    where F: FnOnce(&mut CborDecoder<R>) -> CborResult<T> {
        f(self)
    }

    fn read_option<T, F>(&mut self, mut f: F) -> CborResult<T>
            where F: FnMut(&mut CborDecoder<R>, bool) -> CborResult<T> {
        let b = try!(self.rdr.read_u8());
        if (b & 0b111_00000) >> 5 == 7 && b & 0b000_11111 == 22 {
            f(self, false)
        } else {
            self.rdr.push_byte(b);
            f(self, true)
        }
    }

    fn read_seq<T, F>(&mut self, f: F) -> CborResult<T>
            where F: FnOnce(&mut CborDecoder<R>, usize) -> CborResult<T> {
        let b = try!(self.read_type(Type::Array));
        let len = try!(self.read_len(Some(b)));
        f(self, len)
    }

    fn read_seq_elt<T, F>(&mut self, _idx: usize, f: F) -> CborResult<T>
            where F: FnOnce(&mut CborDecoder<R>) -> CborResult<T> {
        f(self)
    }

    fn read_map<T, F>(&mut self, f: F) -> CborResult<T>
            where F: FnOnce(&mut CborDecoder<R>, usize) -> CborResult<T> {
        let b = try!(self.read_type(Type::Map));
        let len = try!(self.read_len(Some(b)));
        f(self, len)
    }

    fn read_map_elt_key<T, F>(&mut self, _idx: usize, f: F) -> CborResult<T>
            where F: FnOnce(&mut CborDecoder<R>) -> CborResult<T> {
        f(self)
    }

    fn read_map_elt_val<T, F>(&mut self, _idx: usize, f: F) -> CborResult<T>
            where F: FnOnce(&mut CborDecoder<R>) -> CborResult<T> {
        f(self)
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

    fn read_full(&mut self, buf: &mut [u8]) -> io::Result<()> {
        let mut n = 0usize;
        while n < buf.len() {
            n += try!(self.read(&mut buf[n..]));
        }
        Ok(())
    }

    fn push_byte(&mut self, b: u8) {
        self.buf.push(b);
    }
}

fn vec_from_elem<T: Copy>(len: usize, v: T) -> Vec<T> {
    let mut xs = Vec::with_capacity(len);
    unsafe { xs.set_len(len); }
    for x in &mut xs { *x = v; }
    xs
}
