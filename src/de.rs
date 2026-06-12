//! Serde deserialization support for CBOR.

use std::io::Read;

use serde::de::{self, value::BytesDeserializer, Deserializer as _};

use crate::core::{simple, tag, Decoder, Header};
use crate::tag::TagAccess;

/// An error that occurred during deserialization.
#[derive(Debug)]
pub enum Error {
    /// An error from the underlying reader.
    Io(std::io::Error),

    /// The input is not well-formed CBOR.
    ///
    /// Contains the byte offset of the offending item.
    Syntax(usize),

    /// The input is well-formed CBOR but invalid for the target type.
    ///
    /// Contains a description of the error and (optionally) the byte offset
    /// of the item being processed when the error occurred.
    Semantic(Option<usize>, String),

    /// The input is nested deeper than the configured recursion limit.
    ///
    /// This error prevents stack exhaustion from adversarial input.
    RecursionLimitExceeded,
}

impl Error {
    /// A helper for composing a semantic error.
    #[inline]
    pub fn semantic(offset: impl Into<Option<usize>>, msg: impl Into<String>) -> Self {
        Self::Semantic(offset.into(), msg.into())
    }
}

impl From<std::io::Error> for Error {
    #[inline]
    fn from(value: std::io::Error) -> Self {
        Self::Io(value)
    }
}

impl From<crate::core::Error> for Error {
    #[inline]
    fn from(value: crate::core::Error) -> Self {
        match value {
            crate::core::Error::Io(x) => Self::Io(x),
            crate::core::Error::Syntax(x) => Self::Syntax(x),
        }
    }
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Error::Io(err) => write!(f, "i/o error: {err}"),
            Error::Syntax(offset) => write!(f, "syntax error at offset {offset}"),
            Error::Semantic(Some(offset), msg) => {
                write!(f, "semantic error at offset {offset}: {msg}")
            }
            Error::Semantic(None, msg) => write!(f, "semantic error: {msg}"),
            Error::RecursionLimitExceeded => write!(f, "recursion limit exceeded"),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Error::Io(err) => Some(err),
            _ => None,
        }
    }
}

impl de::Error for Error {
    #[inline]
    fn custom<U: core::fmt::Display>(msg: U) -> Self {
        Self::Semantic(None, msg.to_string())
    }
}

trait Expected {
    fn expected(self, kind: &'static str) -> Error;
}

impl Expected for Header {
    #[inline]
    fn expected(self, kind: &'static str) -> Error {
        de::Error::invalid_type(
            match self {
                Header::Positive(x) => de::Unexpected::Unsigned(x),
                Header::Negative(x) => de::Unexpected::Signed(x as i64 ^ !0),
                Header::Bytes(..) => de::Unexpected::Other("bytes"),
                Header::Text(..) => de::Unexpected::Other("string"),

                Header::Array(..) => de::Unexpected::Seq,
                Header::Map(..) => de::Unexpected::Map,

                Header::Tag(..) => de::Unexpected::Other("tag"),

                Header::Simple(simple::FALSE) => de::Unexpected::Bool(false),
                Header::Simple(simple::TRUE) => de::Unexpected::Bool(true),
                Header::Simple(simple::NULL) => de::Unexpected::Other("null"),
                Header::Simple(simple::UNDEFINED) => de::Unexpected::Other("undefined"),
                Header::Simple(..) => de::Unexpected::Other("simple"),

                Header::Float(x) => de::Unexpected::Float(x),
                Header::Break => de::Unexpected::Other("break"),
            },
            &kind,
        )
    }
}

// A parsed integer item: either a (possibly negative) integer that was
// encoded with major type 0 or 1, or a bignum (tag 2 or 3) whose payload is
// given with leading zeros stripped.
enum Num {
    Pos(u64),
    Neg(u64),
    BigPos(Vec<u8>),
    BigNeg(Vec<u8>),
}

// Interprets a stripped bignum payload as a `u128`, if it fits.
fn big_to_u128(bytes: &[u8]) -> Option<u128> {
    if bytes.len() > 16 {
        return None;
    }

    let mut buffer = [0u8; 16];
    buffer[16 - bytes.len()..].copy_from_slice(bytes);
    Some(u128::from_be_bytes(buffer))
}

/// A serde deserializer that reads CBOR from a [`std::io::Read`].
pub struct Deserializer<R> {
    decoder: Decoder<R>,
    scratch: Vec<u8>,
    recurse: usize,
}

/// The default recursion limit for nested CBOR items.
pub const DEFAULT_RECURSION_LIMIT: usize = 256;

impl<R: Read> Deserializer<R> {
    /// Creates a deserializer with the default recursion limit.
    ///
    /// For repeated small reads consider wrapping the reader in a
    /// [`std::io::BufReader`].
    pub fn from_reader(reader: R) -> Self {
        Self::with_recursion_limit(reader, DEFAULT_RECURSION_LIMIT)
    }

    /// Creates a deserializer with the given recursion limit.
    ///
    /// Inputs nested deeper than the limit fail with
    /// [`Error::RecursionLimitExceeded`]. Set a high limit at your own risk
    /// of stack exhaustion.
    pub fn with_recursion_limit(reader: R, limit: usize) -> Self {
        Self {
            decoder: reader.into(),
            scratch: Vec::new(),
            recurse: limit,
        }
    }

    /// Returns the byte offset of the next item in the stream.
    #[inline]
    pub fn offset(&self) -> usize {
        self.decoder.offset()
    }

    /// Turns this deserializer into an iterator over consecutive top-level
    /// items.
    ///
    /// CBOR allows concatenating encoded items into a *sequence* (RFC 8742).
    /// The iterator yields decoded items until the input is exhausted; a
    /// clean end of input terminates the iterator, while anything else
    /// (including a truncated item) yields an error.
    // Named for symmetry with `serde_json::Deserializer::into_iter`.
    #[allow(clippy::should_implement_trait)]
    pub fn into_iter<T: de::DeserializeOwned>(self) -> Iter<T, R> {
        Iter {
            de: self,
            _marker: core::marker::PhantomData,
        }
    }

    #[inline]
    fn recurse<V, F: FnOnce(&mut Self) -> Result<V, Error>>(
        &mut self,
        func: F,
    ) -> Result<V, Error> {
        if self.recurse == 0 {
            return Err(Error::RecursionLimitExceeded);
        }

        self.recurse -= 1;
        let result = func(self);
        self.recurse += 1;
        result
    }

    // Pulls the next integer item, skipping any tags other than the bignum
    // tags. `header` optionally supplies an already-pulled header.
    fn number(&mut self, mut header: Option<Header>) -> Result<Num, Error> {
        loop {
            let header = match header.take() {
                Some(h) => h,
                None => self.decoder.pull()?,
            };

            let neg = match header {
                Header::Positive(x) => return Ok(Num::Pos(x)),
                Header::Negative(x) => return Ok(Num::Neg(x)),
                Header::Tag(tag::BIGPOS) => false,
                Header::Tag(tag::BIGNEG) => true,
                Header::Tag(..) => continue,
                header => return Err(header.expected("integer")),
            };

            let mut bytes = Vec::new();
            match self.decoder.pull()? {
                Header::Bytes(len) => self.decoder.bytes_body(len, &mut bytes)?,
                header => return Err(header.expected("bytes")),
            }

            // An empty payload encodes zero (RFC 8949 §3.4.3); strip
            // leading zeros so the length reflects the magnitude.
            let first = bytes.iter().position(|&b| b != 0).unwrap_or(bytes.len());
            bytes.drain(..first);

            return Ok(match neg {
                false => Num::BigPos(bytes),
                true => Num::BigNeg(bytes),
            });
        }
    }

    fn unsigned(&mut self) -> Result<u128, Error> {
        match self.number(None)? {
            Num::Pos(x) => Ok(x.into()),
            Num::BigPos(b) => big_to_u128(&b).ok_or_else(|| de::Error::custom("bigint too large")),
            _ => Err(de::Error::custom("unexpected negative integer")),
        }
    }

    fn signed(&mut self) -> Result<i128, Error> {
        let raw = match self.number(None)? {
            Num::Pos(x) => return Ok(x.into()),
            Num::Neg(x) => return Ok(x as i128 ^ !0),
            Num::BigPos(b) => {
                return big_to_u128(&b)
                    .and_then(|x| i128::try_from(x).ok())
                    .ok_or_else(|| de::Error::custom("integer too large"));
            }
            Num::BigNeg(b) => {
                big_to_u128(&b).ok_or_else(|| Error::semantic(None, "integer too large"))?
            }
        };

        match i128::try_from(raw) {
            Ok(x) => Ok(x ^ !0),
            Err(..) => Err(de::Error::custom("integer too large")),
        }
    }
}

impl<'de, R: Read> de::Deserializer<'de> for &mut Deserializer<R> {
    type Error = Error;

    #[inline]
    fn deserialize_any<V: de::Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        let header = self.decoder.pull()?;
        self.decoder.push(header);

        match header {
            Header::Positive(..) => self.deserialize_u64(visitor),
            Header::Negative(x) => match i64::try_from(x) {
                Ok(..) => self.deserialize_i64(visitor),
                Err(..) => self.deserialize_i128(visitor),
            },

            Header::Bytes(..) => self.deserialize_byte_buf(visitor),
            Header::Text(..) => self.deserialize_string(visitor),

            Header::Array(..) => self.deserialize_seq(visitor),
            Header::Map(..) => self.deserialize_map(visitor),

            Header::Tag(tag) => {
                let _: Header = self.decoder.pull()?;

                match tag {
                    // Bignums lossy-coerce into plain integers whenever they
                    // fit; otherwise they survive as a tagged byte string.
                    tag::BIGPOS | tag::BIGNEG => match self.number(Some(Header::Tag(tag)))? {
                        Num::BigPos(b) => match big_to_u128(&b) {
                            Some(x) => visitor.visit_u128(x),
                            None => {
                                let access = TagAccess::new(BytesDeserializer::new(&b), Some(tag));
                                visitor.visit_enum(access)
                            }
                        },
                        Num::BigNeg(b) => {
                            match big_to_u128(&b).and_then(|x| i128::try_from(x).ok()) {
                                Some(x) => visitor.visit_i128(x ^ !0),
                                None => {
                                    let access =
                                        TagAccess::new(BytesDeserializer::new(&b), Some(tag));
                                    visitor.visit_enum(access)
                                }
                            }
                        }
                        _ => unreachable!(),
                    },

                    _ => self.recurse(|me| {
                        let access = TagAccess::new(me, Some(tag));
                        visitor.visit_enum(access)
                    }),
                }
            }

            Header::Float(..) => self.deserialize_f64(visitor),

            Header::Simple(simple::FALSE) => self.deserialize_bool(visitor),
            Header::Simple(simple::TRUE) => self.deserialize_bool(visitor),
            Header::Simple(simple::NULL) => self.deserialize_option(visitor),
            Header::Simple(simple::UNDEFINED) => self.deserialize_option(visitor),
            h @ Header::Simple(..) => Err(h.expected("known simple value")),

            h @ Header::Break => Err(h.expected("non-break")),
        }
    }

    #[inline]
    fn deserialize_bool<V: de::Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        loop {
            let offset = self.decoder.offset();

            return match self.decoder.pull()? {
                Header::Tag(..) => continue,
                Header::Simple(simple::FALSE) => visitor.visit_bool(false),
                Header::Simple(simple::TRUE) => visitor.visit_bool(true),
                _ => Err(Error::semantic(offset, "expected bool")),
            };
        }
    }

    #[inline]
    fn deserialize_f32<V: de::Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        self.deserialize_f64(visitor)
    }

    #[inline]
    fn deserialize_f64<V: de::Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        loop {
            return match self.decoder.pull()? {
                Header::Tag(..) => continue,
                Header::Float(x) => visitor.visit_f64(x),
                h => Err(h.expected("float")),
            };
        }
    }

    fn deserialize_i8<V: de::Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        self.deserialize_i64(visitor)
    }

    fn deserialize_i16<V: de::Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        self.deserialize_i64(visitor)
    }

    fn deserialize_i32<V: de::Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        self.deserialize_i64(visitor)
    }

    fn deserialize_i64<V: de::Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        match self.signed()?.try_into() {
            Ok(x) => visitor.visit_i64(x),
            Err(..) => Err(de::Error::custom("integer too large")),
        }
    }

    fn deserialize_i128<V: de::Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        visitor.visit_i128(self.signed()?)
    }

    fn deserialize_u8<V: de::Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        self.deserialize_u64(visitor)
    }

    fn deserialize_u16<V: de::Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        self.deserialize_u64(visitor)
    }

    fn deserialize_u32<V: de::Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        self.deserialize_u64(visitor)
    }

    fn deserialize_u64<V: de::Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        match self.unsigned()?.try_into() {
            Ok(x) => visitor.visit_u64(x),
            Err(..) => Err(de::Error::custom("integer too large")),
        }
    }

    fn deserialize_u128<V: de::Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        visitor.visit_u128(self.unsigned()?)
    }

    fn deserialize_char<V: de::Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        loop {
            let offset = self.decoder.offset();
            let header = self.decoder.pull()?;

            return match header {
                Header::Tag(..) => continue,

                Header::Text(Some(len)) if len <= 4 => {
                    let mut buffer = [0u8; 4];
                    self.decoder.read_exact(&mut buffer[..len])?;

                    match core::str::from_utf8(&buffer[..len]) {
                        Ok(s) => match s.chars().count() {
                            1 => visitor.visit_char(s.chars().next().unwrap()),
                            _ => Err(header.expected("char")),
                        },
                        Err(..) => Err(Error::Syntax(offset)),
                    }
                }

                _ => Err(header.expected("char")),
            };
        }
    }

    fn deserialize_str<V: de::Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        self.deserialize_string(visitor)
    }

    fn deserialize_string<V: de::Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        loop {
            return match self.decoder.pull()? {
                Header::Tag(..) => continue,

                Header::Text(len) => {
                    let mut buffer = String::new();
                    self.decoder.text_body(len, &mut buffer)?;
                    visitor.visit_string(buffer)
                }

                header => Err(header.expected("string")),
            };
        }
    }

    fn deserialize_bytes<V: de::Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        self.deserialize_byte_buf(visitor)
    }

    fn deserialize_byte_buf<V: de::Visitor<'de>>(
        self,
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        loop {
            return match self.decoder.pull()? {
                Header::Tag(..) => continue,

                Header::Bytes(len) => {
                    let mut buffer = Vec::new();
                    self.decoder.bytes_body(len, &mut buffer)?;
                    visitor.visit_byte_buf(buffer)
                }

                // Be liberal: accept an array of integers as bytes.
                Header::Array(len) => self.recurse(|me| visitor.visit_seq(Access(me, len))),

                header => Err(header.expected("bytes")),
            };
        }
    }

    fn deserialize_seq<V: de::Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        loop {
            return match self.decoder.pull()? {
                Header::Tag(..) => continue,

                Header::Array(len) => self.recurse(|me| visitor.visit_seq(Access(me, len))),

                // Be liberal: accept a byte string as a sequence of integers.
                Header::Bytes(len) => {
                    let mut buffer = Vec::new();
                    self.decoder.bytes_body(len, &mut buffer)?;
                    visitor.visit_seq(BytesAccess(0, buffer))
                }

                header => Err(header.expected("array")),
            };
        }
    }

    fn deserialize_map<V: de::Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        loop {
            return match self.decoder.pull()? {
                Header::Tag(..) => continue,
                Header::Map(len) => self.recurse(|me| visitor.visit_map(Access(me, len))),
                header => Err(header.expected("map")),
            };
        }
    }

    fn deserialize_struct<V: de::Visitor<'de>>(
        self,
        _name: &'static str,
        _fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        self.deserialize_map(visitor)
    }

    fn deserialize_tuple<V: de::Visitor<'de>>(
        self,
        _len: usize,
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        self.deserialize_seq(visitor)
    }

    fn deserialize_tuple_struct<V: de::Visitor<'de>>(
        self,
        _name: &'static str,
        _len: usize,
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        self.deserialize_seq(visitor)
    }

    fn deserialize_identifier<V: de::Visitor<'de>>(
        self,
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        loop {
            let offset = self.decoder.offset();

            return match self.decoder.pull()? {
                Header::Tag(..) => continue,

                Header::Text(Some(len)) => {
                    self.scratch.clear();
                    self.decoder.bytes_body(Some(len), &mut self.scratch)?;

                    match core::str::from_utf8(&self.scratch) {
                        Ok(s) => visitor.visit_str(s),
                        Err(..) => Err(Error::Syntax(offset)),
                    }
                }

                Header::Bytes(Some(len)) => {
                    self.scratch.clear();
                    self.decoder.bytes_body(Some(len), &mut self.scratch)?;
                    visitor.visit_bytes(&self.scratch)
                }

                header => Err(header.expected("str or bytes")),
            };
        }
    }

    fn deserialize_ignored_any<V: de::Visitor<'de>>(
        self,
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        self.deserialize_any(visitor)
    }

    #[inline]
    fn deserialize_option<V: de::Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        match self.decoder.pull()? {
            Header::Simple(simple::UNDEFINED) => visitor.visit_none(),
            Header::Simple(simple::NULL) => visitor.visit_none(),
            header => {
                self.decoder.push(header);
                visitor.visit_some(self)
            }
        }
    }

    #[inline]
    fn deserialize_unit<V: de::Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        loop {
            return match self.decoder.pull()? {
                Header::Simple(simple::UNDEFINED) => visitor.visit_unit(),
                Header::Simple(simple::NULL) => visitor.visit_unit(),
                Header::Tag(..) => continue,
                header => Err(header.expected("unit")),
            };
        }
    }

    #[inline]
    fn deserialize_unit_struct<V: de::Visitor<'de>>(
        self,
        _name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        self.deserialize_unit(visitor)
    }

    #[inline]
    fn deserialize_newtype_struct<V: de::Visitor<'de>>(
        self,
        _name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        visitor.visit_newtype_struct(self)
    }

    #[inline]
    fn deserialize_enum<V: de::Visitor<'de>>(
        self,
        name: &'static str,
        _variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        if name == crate::tag::NAME {
            let tag = match self.decoder.pull()? {
                Header::Tag(x) => Some(x),
                header => {
                    self.decoder.push(header);
                    None
                }
            };

            return self.recurse(|me| visitor.visit_enum(TagAccess::new(me, tag)));
        }

        loop {
            // An enum variant is either encoded as a map with a single entry
            // (the variant name and its payload) or, for a unit variant, as
            // a bare text string.
            let map = match self.decoder.pull()? {
                Header::Tag(..) => continue,
                Header::Map(Some(1)) => true,
                header @ Header::Text(..) => {
                    self.decoder.push(header);
                    false
                }
                header => return Err(header.expected("enum")),
            };

            return self.recurse(|me| visitor.visit_enum(Enum(me, map)));
        }
    }

    #[inline]
    fn is_human_readable(&self) -> bool {
        false
    }
}

struct Access<'a, R>(&'a mut Deserializer<R>, Option<usize>);

impl<'de, R: Read> de::SeqAccess<'de> for Access<'_, R> {
    type Error = Error;

    #[inline]
    fn next_element_seed<U: de::DeserializeSeed<'de>>(
        &mut self,
        seed: U,
    ) -> Result<Option<U::Value>, Self::Error> {
        match self.1 {
            Some(0) => return Ok(None),
            Some(x) => self.1 = Some(x - 1),
            None => match self.0.decoder.pull()? {
                Header::Break => return Ok(None),
                header => self.0.decoder.push(header),
            },
        }

        seed.deserialize(&mut *self.0).map(Some)
    }

    #[inline]
    fn size_hint(&self) -> Option<usize> {
        self.1
    }
}

impl<'de, R: Read> de::MapAccess<'de> for Access<'_, R> {
    type Error = Error;

    #[inline]
    fn next_key_seed<K: de::DeserializeSeed<'de>>(
        &mut self,
        seed: K,
    ) -> Result<Option<K::Value>, Self::Error> {
        match self.1 {
            Some(0) => return Ok(None),
            Some(x) => self.1 = Some(x - 1),
            None => match self.0.decoder.pull()? {
                Header::Break => return Ok(None),
                header => self.0.decoder.push(header),
            },
        }

        seed.deserialize(&mut *self.0).map(Some)
    }

    #[inline]
    fn next_value_seed<V: de::DeserializeSeed<'de>>(
        &mut self,
        seed: V,
    ) -> Result<V::Value, Self::Error> {
        seed.deserialize(&mut *self.0)
    }

    #[inline]
    fn size_hint(&self) -> Option<usize> {
        self.1
    }
}

// Variant access for an enum item.
//
// The boolean field indicates whether the variant was encoded as a
// single-entry map (`true`) or as a bare text string (`false`). The bare
// form only encodes a unit variant, so payload accesses in that form must
// not consume any further items from the stream.
struct Enum<'a, R>(&'a mut Deserializer<R>, bool);

impl<'de, R: Read> de::EnumAccess<'de> for Enum<'_, R> {
    type Error = Error;
    type Variant = Self;

    #[inline]
    fn variant_seed<V: de::DeserializeSeed<'de>>(
        self,
        seed: V,
    ) -> Result<(V::Value, Self::Variant), Self::Error> {
        let variant = seed.deserialize(&mut *self.0)?;
        Ok((variant, self))
    }
}

impl<'de, R: Read> de::VariantAccess<'de> for Enum<'_, R> {
    type Error = Error;

    #[inline]
    fn unit_variant(self) -> Result<(), Self::Error> {
        if self.1 {
            // The map form carries a payload; require it to be a unit.
            <() as de::Deserialize>::deserialize(&mut *self.0)?;
        }

        Ok(())
    }

    #[inline]
    fn newtype_variant_seed<U: de::DeserializeSeed<'de>>(
        self,
        seed: U,
    ) -> Result<U::Value, Self::Error> {
        if !self.1 {
            return Err(de::Error::invalid_type(
                de::Unexpected::UnitVariant,
                &"newtype variant",
            ));
        }

        seed.deserialize(&mut *self.0)
    }

    #[inline]
    fn tuple_variant<V: de::Visitor<'de>>(
        self,
        _len: usize,
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        if !self.1 {
            return Err(de::Error::invalid_type(
                de::Unexpected::UnitVariant,
                &"tuple variant",
            ));
        }

        self.0.deserialize_seq(visitor)
    }

    #[inline]
    fn struct_variant<V: de::Visitor<'de>>(
        self,
        _fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        if !self.1 {
            return Err(de::Error::invalid_type(
                de::Unexpected::UnitVariant,
                &"struct variant",
            ));
        }

        self.0.deserialize_map(visitor)
    }
}

// Yields the contents of a byte string as a sequence of integers.
struct BytesAccess(usize, Vec<u8>);

impl<'de> de::SeqAccess<'de> for BytesAccess {
    type Error = Error;

    #[inline]
    fn next_element_seed<U: de::DeserializeSeed<'de>>(
        &mut self,
        seed: U,
    ) -> Result<Option<U::Value>, Self::Error> {
        use de::IntoDeserializer;

        if self.0 < self.1.len() {
            let byte = self.1[self.0];
            self.0 += 1;
            seed.deserialize(byte.into_deserializer()).map(Some)
        } else {
            Ok(None)
        }
    }

    #[inline]
    fn size_hint(&self) -> Option<usize> {
        Some(self.1.len() - self.0)
    }
}

/// An iterator decoding consecutive top-level items from a reader.
///
/// Created by [`Deserializer::into_iter`].
pub struct Iter<T, R> {
    de: Deserializer<R>,
    _marker: core::marker::PhantomData<T>,
}

impl<T: de::DeserializeOwned, R: Read> Iterator for Iter<T, R> {
    type Item = Result<T, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        let start = self.de.decoder.offset();

        // Probe for a clean end of input: end-of-file before the first byte
        // of an item terminates the stream, anywhere else it is an error.
        match self.de.decoder.pull() {
            Ok(header) => self.de.decoder.push(header),
            Err(crate::core::Error::Io(err))
                if err.kind() == std::io::ErrorKind::UnexpectedEof
                    && self.de.decoder.offset() == start =>
            {
                return None;
            }
            Err(err) => return Some(Err(err.into())),
        }

        Some(T::deserialize(&mut self.de))
    }
}

/// Deserializes a value from CBOR read out of a [`std::io::Read`].
///
/// For repeated small reads consider wrapping the reader in a
/// [`std::io::BufReader`].
#[inline]
pub fn from_reader<T: de::DeserializeOwned, R: Read>(reader: R) -> Result<T, Error> {
    let mut deserializer = Deserializer::from_reader(reader);
    T::deserialize(&mut deserializer)
}

/// Deserializes a value from a byte slice of CBOR.
#[inline]
pub fn from_slice<T: de::DeserializeOwned>(slice: &[u8]) -> Result<T, Error> {
    from_reader(slice)
}
