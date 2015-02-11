use std::borrow::ToOwned;
use std::char;

use rustc_serialize::Decodable;
use rustc_serialize::Decoder as RustcDecoder;

use {
    Cbor, Type,
    CborResult, CborError, ReadError,
    Reader,
};

pub trait CborDecodable {
    fn cbor_decode(d: &mut Decoder) -> CborResult<Self>;
}

impl<D: Decodable> CborDecodable for D {
    fn cbor_decode(d: &mut Decoder) -> CborResult<D> {
        Decodable::decode(d)
    }
}

pub struct Decoder {
    stack: Vec<Cbor>,
}

impl Decoder {
    pub fn new(val: Cbor) -> Decoder {
        Decoder { stack: vec![val] }
    }

    fn pop(&mut self, expected: Type) -> CborResult<Cbor> {
        match self.stack.pop() {
            Some(v) => Ok(v),
            None => Err(self.errstr(format!(
                "No data items left (expected a data item with type '{:?}').",
                expected))),
        }
    }

    fn pop_expect(&mut self, expected: &str) -> CborResult<Cbor> {
        match self.stack.pop() {
            Some(v) => Ok(v),
            None => Err(self.errstr(format!(
                "No data items left (expected {}).", expected))),
        }
    }

    fn err(&self, err: ReadError) -> CborError {
        CborError::Decode(err)
    }

    fn errstr(&self, s: String) -> CborError {
        self.err(ReadError::Other(s))
    }
}

macro_rules! read_unsigned {
    ($dec:ident, $cbor_ty:expr, $to:ident) => ({
        let v = try!($dec.pop($cbor_ty));
        match v {
            Cbor::Unsigned(v) => v.$to().map_err(CborError::Decode),
            ref v => return Err($dec.err(ReadError::mismatch($cbor_ty, v))),
        }
    });
}

macro_rules! read_signed {
    ($dec:ident, $ty:ty, $cbor_ty:expr, $to:ident, $tou:ident) => ({
        let v = try!($dec.pop($cbor_ty));
        match v {
            Cbor::Signed(v) => v.$to().map_err(CborError::Decode),
            Cbor::Unsigned(v) =>
                v.$tou().map(|n| n as $ty).map_err(CborError::Decode),
            ref v => return Err($dec.err(ReadError::mismatch($cbor_ty, v))),
        }
    });
}

macro_rules! read_float {
    ($dec:ident, $ty:ty, $cbor_ty:expr,
     $to:ident, $toi:ident, $tou:ident) => ({
        let v = try!($dec.pop($cbor_ty));
        match v {
            Cbor::Float(v) => v.$to().map_err(CborError::Decode),
            Cbor::Signed(v) =>
                v.$toi().map(|n| n as $ty).map_err(CborError::Decode),
            Cbor::Unsigned(v) =>
                v.$tou().map(|n| n as $ty).map_err(CborError::Decode),
            ref v => return Err($dec.err(ReadError::mismatch($cbor_ty, v))),
        }
    });
}

impl RustcDecoder for Decoder {
    type Error = CborError;

    fn error(&mut self, err: &str) -> CborError {
        self.err(ReadError::Other(err.to_owned()))
    }

    fn read_nil(&mut self) -> CborResult<()> {
        match try!(self.pop(Type::Null)) {
            Cbor::Null => Ok(()),
            v => Err(self.err(ReadError::mismatch(Type::Null, &v))),
        }
    }

    fn read_usize(&mut self) -> CborResult<usize> {
        read_unsigned!(self, Type::UInt, to_usize)
    }

    fn read_u64(&mut self) -> CborResult<u64> {
        read_unsigned!(self, Type::UInt64, to_u64)
    }

    fn read_u32(&mut self) -> CborResult<u32> {
        read_unsigned!(self, Type::UInt32, to_u32)
    }

    fn read_u16(&mut self) -> CborResult<u16> {
        read_unsigned!(self, Type::UInt16, to_u16)
    }

    fn read_u8(&mut self) -> CborResult<u8> {
        read_unsigned!(self, Type::UInt8, to_u8)
    }

    fn read_isize(&mut self) -> CborResult<isize> {
        read_signed!(self, isize, Type::Int, to_isize, to_usize)
    }

    fn read_i64(&mut self) -> CborResult<i64> {
        read_signed!(self, i64, Type::Int64, to_i64, to_u64)
    }

    fn read_i32(&mut self) -> CborResult<i32> {
        read_signed!(self, i32, Type::Int32, to_i32, to_u32)
    }

    fn read_i16(&mut self) -> CborResult<i16> {
        read_signed!(self, i16, Type::Int16, to_i16, to_u16)
    }

    fn read_i8(&mut self) -> CborResult<i8> {
        read_signed!(self, i8, Type::Int8, to_i8, to_u8)
    }

    fn read_bool(&mut self) -> CborResult<bool> {
        match try!(self.pop(Type::Bool)) {
            Cbor::Bool(s) => Ok(s),
            v => Err(self.err(ReadError::mismatch(Type::Bool, &v))),
        }
    }

    fn read_f64(&mut self) -> CborResult<f64> {
        read_float!(self, f64, Type::Float64, to_f64, to_i64, to_u64)
    }

    fn read_f32(&mut self) -> CborResult<f32> {
        read_float!(self, f32, Type::Float32, to_f32, to_i32, to_u32)
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
        match try!(self.pop(Type::Unicode)) {
            Cbor::Unicode(s) => Ok(s),
            v => Err(self.err(ReadError::mismatch(Type::Unicode, &v))),
        }
    }

    fn read_enum<T, F>(&mut self, name: &str, f: F) -> CborResult<T>
            where F: FnOnce(&mut Decoder) -> CborResult<T> {
        f(self)
    }

    fn read_enum_variant<T, F>(
        &mut self,
        names: &[&str],
        mut f: F,
    ) -> CborResult<T>
    where F: FnMut(&mut Decoder, usize) -> CborResult<T> {
        let name = match try!(self.pop_expect("Unicode or variant map")) {
            Cbor::Unicode(name) => name,
            Cbor::Map(mut map) => {
                let name = match map.remove("variant") {
                    Some(Cbor::Unicode(name)) => name,
                    Some(v) => return Err(self.errstr(format!(
                        "Expected 'variant' key in variant map to map to a \
                         Unicode string, but got {:?}", v.typ()))),
                    None => return Err(self.errstr(format!(
                        "Missing 'variant' key in variant map"))),
                };
                match map.remove("fields") {
                    Some(Cbor::Array(fields)) => {
                        self.stack.extend(fields.into_iter().rev());
                    },
                    Some(v) => return Err(self.errstr(format!(
                        "Expected 'fields' key in variant map to map to an \
                         Array, but got {:?}", v.typ()))),
                    None => return Err(self.errstr(format!(
                        "Missing 'fields' key in variant map."))),
                }
                name
            }
            v => return Err(self.errstr(format!(
                "Expected Unicode string or variant map, but got {:?}",
                v.typ()))),
        };
        let idx = match names.iter().position(|&n| n == name) {
            Some(idx) => idx,
            None => return Err(self.errstr(format!(
                "Unknown variant name '{}'.", name))),
        };
        f(self, idx)
    }

    fn read_enum_variant_arg<T, F>(
        &mut self,
        a_idx: usize,
        f: F,
    ) -> CborResult<T>
    where F: FnOnce(&mut Decoder) -> CborResult<T> {
        f(self)
    }

    fn read_enum_struct_variant<T, F>(
        &mut self,
        names: &[&str],
        f: F,
    ) -> CborResult<T>
    where F: FnMut(&mut Decoder, usize) -> CborResult<T> {
        self.read_enum_variant(names, f)
    }

    fn read_enum_struct_variant_field<T, F>(
        &mut self,
        f_name: &str,
        f_idx: usize,
        f: F,
    ) -> CborResult<T>
    where F: FnOnce(&mut Decoder) -> CborResult<T> {
        self.read_enum_variant_arg(f_idx, f)
    }

    fn read_struct<T, F>(
        &mut self,
        s_name: &str,
        len: usize,
        f: F,
    ) -> CborResult<T>
    where F: FnOnce(&mut Decoder) -> CborResult<T> {
        let val = try!(f(self));
        // When we read a struct field, we pop the CBOR map off the stack,
        // find and remove the field name and its associated value, and then
        // push the map back on the stack. Therefore, when we're done
        // processing all the struct fields, we'll have an extraneous map
        // left on the stack. So pop it off. If this assert fails, we have a
        // bug in the decoder. ---AG
        assert_eq!(self.stack.pop().unwrap().typ(), Type::Map);
        // Do we want to check if the map popped off here is empty? If it's
        // not, that means the data contains more than what the struct
        // specifies. We should probably be relaxed and let it pass. ---AG
        Ok(val)
    }

    fn read_struct_field<T, F>(
        &mut self,
        f_name: &str,
        f_idx: usize,
        f: F,
    ) -> CborResult<T>
    where F: FnOnce(&mut Decoder) -> CborResult<T> {
        let mut map = match try!(self.pop(Type::Map)) {
            Cbor::Map(map) => map,
            v => return Err(self.err(ReadError::mismatch(Type::Map, &v))),
        };
        let val = match map.remove(f_name) {
            Some(val) => { self.stack.push(val); try!(f(self)) }
            None => {
                self.stack.push(Cbor::Null);
                match f(self) {
                    Ok(val) => val,
                    Err(_) => return Err(self.errstr(format!(
                        "Missing field '{}' in map object.", f_name))),
                }
            }
        };
        self.stack.push(Cbor::Map(map));
        Ok(val)
    }

    fn read_tuple<T, F>(
        &mut self,
        len: usize,
        f: F,
    ) -> CborResult<T>
    where F: FnOnce(&mut Decoder) -> CborResult<T> {
        let array = match try!(self.pop(Type::Array)) {
            Cbor::Array(v) => v,
            v => return Err(self.err(ReadError::mismatch(Type::Array, &v))),
        };
        let got_len = array.len();
        if len != got_len {
            return Err(self.errstr(format!(
                "Expected tuple of length {:?}, but got array of length {:?}",
                len, got_len)));
        }
        self.stack.extend(array.into_iter().rev());
        f(self)
    }

    fn read_tuple_arg<T, F>(
        &mut self,
        a_idx: usize,
        f: F,
    ) -> CborResult<T>
    where F: FnOnce(&mut Decoder) -> CborResult<T> {
        f(self)
    }

    fn read_tuple_struct<T, F>(
        &mut self,
        s_name: &str,
        len: usize,
        f: F,
    ) -> CborResult<T>
    where F: FnOnce(&mut Decoder) -> CborResult<T> {
        let array = match try!(self.pop(Type::Array)) {
            Cbor::Array(v) => v,
            v => return Err(self.err(ReadError::mismatch(Type::Array, &v))),
        };
        let got_len = array.len();
        if len != got_len {
            return Err(self.errstr(format!(
                "Expected tuple of length {:?}, but got array of length {:?}",
                len, got_len)));
        }
        self.stack.extend(array.into_iter().rev());
        f(self)
    }

    fn read_tuple_struct_arg<T, F>(
        &mut self,
        a_idx: usize,
        f: F,
    ) -> CborResult<T>
    where F: FnOnce(&mut Decoder) -> CborResult<T> {
        f(self)
    }

    fn read_option<T, F>(&mut self, mut f: F) -> CborResult<T>
            where F: FnMut(&mut Decoder, bool) -> CborResult<T> {
        match try!(self.pop(Type::Any)) {
            Cbor::Null => f(self, false),
            v => { self.stack.push(v); f(self, true) }
        }
    }

    fn read_seq<T, F>(&mut self, f: F) -> CborResult<T>
            where F: FnOnce(&mut Decoder, usize) -> CborResult<T> {
        let array = match try!(self.pop(Type::Array)) {
            Cbor::Array(v) => v,
            v => return Err(self.err(ReadError::mismatch(Type::Array, &v))),
        };
        let len = array.len();
        self.stack.extend(array.into_iter().rev());
        f(self, len)
    }

    fn read_seq_elt<T, F>(&mut self, idx: usize, f: F) -> CborResult<T>
            where F: FnOnce(&mut Decoder) -> CborResult<T> {
        f(self)
    }

    fn read_map<T, F>(&mut self, f: F) -> CborResult<T>
            where F: FnOnce(&mut Decoder, usize) -> CborResult<T> {
        let map = match try!(self.pop(Type::Map)) {
            Cbor::Map(v) => v,
            v => return Err(self.err(ReadError::mismatch(Type::Map, &v))),
        };
        let len = map.len();
        for (k, v) in map { // order doesn't matter for HashMap
            self.stack.push(v);
            self.stack.push(Cbor::Unicode(k));
        }
        f(self, len)
    }

    fn read_map_elt_key<T, F>(&mut self, idx: usize, f: F) -> CborResult<T>
            where F: FnOnce(&mut Decoder) -> CborResult<T> {
        f(self)
    }

    fn read_map_elt_val<T, F>(&mut self, idx: usize, f: F) -> CborResult<T>
            where F: FnOnce(&mut Decoder) -> CborResult<T> {
        f(self)
    }
}

#[derive(Debug)]
pub struct ByteString(pub Vec<u8>);

impl CborDecodable for ByteString {
    fn cbor_decode(d: &mut Decoder) -> CborResult<ByteString> {
        match try!(d.pop(Type::Bytes)) {
            Cbor::Bytes(s) => Ok(ByteString(s)),
            v => Err(d.err(ReadError::mismatch(Type::Bytes, &v))),
        }
    }
}
