//! Serde serialization support for CBOR.

use std::io::Write;

use serde::ser::{self, Serialize as _};

use crate::core::{simple, tag, Encoder, Header};
use crate::value::KeyOrder;

/// An error that occurred during serialization.
#[derive(Debug)]
pub enum Error {
    /// An error from the underlying writer.
    Io(std::io::Error),

    /// A value cannot be represented in CBOR.
    ///
    /// Contains a description of the problem.
    Value(String),
}

impl From<std::io::Error> for Error {
    #[inline]
    fn from(value: std::io::Error) -> Self {
        Self::Io(value)
    }
}

impl From<crate::value::Error> for Error {
    fn from(value: crate::value::Error) -> Self {
        Self::Value(value.to_string())
    }
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Error::Io(err) => write!(f, "i/o error: {err}"),
            Error::Value(msg) => write!(f, "value error: {msg}"),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Error::Io(err) => Some(err),
            Error::Value(..) => None,
        }
    }
}

impl ser::Error for Error {
    fn custom<U: core::fmt::Display>(msg: U) -> Self {
        Error::Value(msg.to_string())
    }
}

/// A serde serializer that writes CBOR to a [`std::io::Write`].
pub struct Serializer<W>(Encoder<W>);

impl<W: Write> From<W> for Serializer<W> {
    #[inline]
    fn from(writer: W) -> Self {
        Self(writer.into())
    }
}

impl<W: Write> From<Encoder<W>> for Serializer<W> {
    #[inline]
    fn from(encoder: Encoder<W>) -> Self {
        Self(encoder)
    }
}

impl<'a, W: Write> ser::Serializer for &'a mut Serializer<W> {
    type Ok = ();
    type Error = Error;

    type SerializeSeq = CollectionSerializer<'a, W>;
    type SerializeTuple = CollectionSerializer<'a, W>;
    type SerializeTupleStruct = CollectionSerializer<'a, W>;
    type SerializeTupleVariant = CollectionSerializer<'a, W>;
    type SerializeMap = CollectionSerializer<'a, W>;
    type SerializeStruct = CollectionSerializer<'a, W>;
    type SerializeStructVariant = CollectionSerializer<'a, W>;

    #[inline]
    fn serialize_bool(self, v: bool) -> Result<(), Error> {
        Ok(self.0.push(Header::Simple(match v {
            false => simple::FALSE,
            true => simple::TRUE,
        }))?)
    }

    #[inline]
    fn serialize_i8(self, v: i8) -> Result<(), Error> {
        self.serialize_i64(v.into())
    }

    #[inline]
    fn serialize_i16(self, v: i16) -> Result<(), Error> {
        self.serialize_i64(v.into())
    }

    #[inline]
    fn serialize_i32(self, v: i32) -> Result<(), Error> {
        self.serialize_i64(v.into())
    }

    #[inline]
    fn serialize_i64(self, v: i64) -> Result<(), Error> {
        Ok(self.0.push(match v.is_negative() {
            false => Header::Positive(v as u64),
            true => Header::Negative(v as u64 ^ !0),
        })?)
    }

    #[inline]
    fn serialize_i128(self, v: i128) -> Result<(), Error> {
        let (tag, raw) = match v.is_negative() {
            false => (tag::BIGPOS, v as u128),
            true => (tag::BIGNEG, v as u128 ^ !0),
        };

        if let Ok(x) = u64::try_from(raw) {
            return Ok(self.0.push(match tag {
                tag::BIGPOS => Header::Positive(x),
                _ => Header::Negative(x),
            })?);
        }

        let bytes = raw.to_be_bytes();
        let first = raw.leading_zeros() as usize / 8;

        self.0.push(Header::Tag(tag))?;
        Ok(self.0.bytes(&bytes[first..])?)
    }

    #[inline]
    fn serialize_u8(self, v: u8) -> Result<(), Error> {
        self.serialize_u64(v.into())
    }

    #[inline]
    fn serialize_u16(self, v: u16) -> Result<(), Error> {
        self.serialize_u64(v.into())
    }

    #[inline]
    fn serialize_u32(self, v: u32) -> Result<(), Error> {
        self.serialize_u64(v.into())
    }

    #[inline]
    fn serialize_u64(self, v: u64) -> Result<(), Error> {
        Ok(self.0.push(Header::Positive(v))?)
    }

    #[inline]
    fn serialize_u128(self, v: u128) -> Result<(), Error> {
        if let Ok(x) = u64::try_from(v) {
            return self.serialize_u64(x);
        }

        let bytes = v.to_be_bytes();
        let first = v.leading_zeros() as usize / 8;

        self.0.push(Header::Tag(tag::BIGPOS))?;
        Ok(self.0.bytes(&bytes[first..])?)
    }

    #[inline]
    fn serialize_f32(self, v: f32) -> Result<(), Error> {
        self.serialize_f64(v.into())
    }

    #[inline]
    fn serialize_f64(self, v: f64) -> Result<(), Error> {
        Ok(self.0.push(Header::Float(v))?)
    }

    #[inline]
    fn serialize_char(self, v: char) -> Result<(), Error> {
        let mut buffer = [0u8; 4];
        self.serialize_str(v.encode_utf8(&mut buffer))
    }

    #[inline]
    fn serialize_str(self, v: &str) -> Result<(), Error> {
        Ok(self.0.text(v)?)
    }

    #[inline]
    fn serialize_bytes(self, v: &[u8]) -> Result<(), Error> {
        Ok(self.0.bytes(v)?)
    }

    #[inline]
    fn serialize_none(self) -> Result<(), Error> {
        Ok(self.0.push(Header::Simple(simple::NULL))?)
    }

    #[inline]
    fn serialize_some<U: ?Sized + ser::Serialize>(self, value: &U) -> Result<(), Error> {
        value.serialize(self)
    }

    #[inline]
    fn serialize_unit(self) -> Result<(), Error> {
        self.serialize_none()
    }

    #[inline]
    fn serialize_unit_struct(self, _name: &'static str) -> Result<(), Error> {
        self.serialize_unit()
    }

    #[inline]
    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _index: u32,
        variant: &'static str,
    ) -> Result<(), Error> {
        self.serialize_str(variant)
    }

    #[inline]
    fn serialize_newtype_struct<U: ?Sized + ser::Serialize>(
        self,
        _name: &'static str,
        value: &U,
    ) -> Result<(), Error> {
        value.serialize(self)
    }

    #[inline]
    fn serialize_newtype_variant<U: ?Sized + ser::Serialize>(
        self,
        name: &'static str,
        _index: u32,
        variant: &'static str,
        value: &U,
    ) -> Result<(), Error> {
        if name != crate::tag::NAME || variant != crate::tag::UNTAGGED {
            self.0.push(Header::Map(Some(1)))?;
            self.serialize_str(variant)?;
        }

        value.serialize(self)
    }

    #[inline]
    fn serialize_seq(self, length: Option<usize>) -> Result<Self::SerializeSeq, Error> {
        self.0.push(Header::Array(length))?;
        Ok(CollectionSerializer {
            encoder: self,
            ending: length.is_none(),
            tag: false,
        })
    }

    #[inline]
    fn serialize_tuple(self, length: usize) -> Result<Self::SerializeTuple, Error> {
        self.serialize_seq(Some(length))
    }

    #[inline]
    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        length: usize,
    ) -> Result<Self::SerializeTupleStruct, Error> {
        self.serialize_seq(Some(length))
    }

    #[inline]
    fn serialize_tuple_variant(
        self,
        name: &'static str,
        _index: u32,
        variant: &'static str,
        length: usize,
    ) -> Result<Self::SerializeTupleVariant, Error> {
        if name == crate::tag::NAME && variant == crate::tag::TAGGED {
            return Ok(CollectionSerializer {
                encoder: self,
                ending: false,
                tag: true,
            });
        }

        self.0.push(Header::Map(Some(1)))?;
        self.serialize_str(variant)?;
        self.0.push(Header::Array(Some(length)))?;
        Ok(CollectionSerializer {
            encoder: self,
            ending: false,
            tag: false,
        })
    }

    #[inline]
    fn serialize_map(self, length: Option<usize>) -> Result<Self::SerializeMap, Error> {
        self.0.push(Header::Map(length))?;
        Ok(CollectionSerializer {
            encoder: self,
            ending: length.is_none(),
            tag: false,
        })
    }

    #[inline]
    fn serialize_struct(
        self,
        _name: &'static str,
        length: usize,
    ) -> Result<Self::SerializeStruct, Error> {
        self.serialize_map(Some(length))
    }

    #[inline]
    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _index: u32,
        variant: &'static str,
        length: usize,
    ) -> Result<Self::SerializeStructVariant, Error> {
        self.0.push(Header::Map(Some(1)))?;
        self.serialize_str(variant)?;
        self.0.push(Header::Map(Some(length)))?;
        Ok(CollectionSerializer {
            encoder: self,
            ending: false,
            tag: false,
        })
    }

    #[inline]
    fn is_human_readable(&self) -> bool {
        false
    }
}

/// The serializer for CBOR arrays and maps.
pub struct CollectionSerializer<'a, W> {
    encoder: &'a mut Serializer<W>,
    ending: bool,
    tag: bool,
}

impl<W: Write> CollectionSerializer<'_, W> {
    #[inline]
    fn end_inner(self) -> Result<(), Error> {
        if self.ending {
            self.encoder.0.push(Header::Break)?;
        }
        Ok(())
    }
}

impl<W: Write> ser::SerializeSeq for CollectionSerializer<'_, W> {
    type Ok = ();
    type Error = Error;

    #[inline]
    fn serialize_element<U: ?Sized + ser::Serialize>(&mut self, value: &U) -> Result<(), Error> {
        value.serialize(&mut *self.encoder)
    }

    #[inline]
    fn end(self) -> Result<(), Error> {
        self.end_inner()
    }
}

impl<W: Write> ser::SerializeTuple for CollectionSerializer<'_, W> {
    type Ok = ();
    type Error = Error;

    #[inline]
    fn serialize_element<U: ?Sized + ser::Serialize>(&mut self, value: &U) -> Result<(), Error> {
        value.serialize(&mut *self.encoder)
    }

    #[inline]
    fn end(self) -> Result<(), Error> {
        self.end_inner()
    }
}

impl<W: Write> ser::SerializeTupleStruct for CollectionSerializer<'_, W> {
    type Ok = ();
    type Error = Error;

    #[inline]
    fn serialize_field<U: ?Sized + ser::Serialize>(&mut self, value: &U) -> Result<(), Error> {
        value.serialize(&mut *self.encoder)
    }

    #[inline]
    fn end(self) -> Result<(), Error> {
        self.end_inner()
    }
}

impl<W: Write> ser::SerializeTupleVariant for CollectionSerializer<'_, W> {
    type Ok = ();
    type Error = Error;

    #[inline]
    fn serialize_field<U: ?Sized + ser::Serialize>(&mut self, value: &U) -> Result<(), Error> {
        if !self.tag {
            return value.serialize(&mut *self.encoder);
        }

        // The first field of the tag pseudo-variant is the tag number
        // itself; the second is serialized normally.
        self.tag = false;
        match value.serialize(crate::tag::TagNumberSerializer) {
            Ok(x) => Ok(self.encoder.0.push(Header::Tag(x))?),
            Err(..) => Err(Error::Value("expected tag".into())),
        }
    }

    #[inline]
    fn end(self) -> Result<(), Error> {
        self.end_inner()
    }
}

impl<W: Write> ser::SerializeMap for CollectionSerializer<'_, W> {
    type Ok = ();
    type Error = Error;

    #[inline]
    fn serialize_key<U: ?Sized + ser::Serialize>(&mut self, key: &U) -> Result<(), Error> {
        key.serialize(&mut *self.encoder)
    }

    #[inline]
    fn serialize_value<U: ?Sized + ser::Serialize>(&mut self, value: &U) -> Result<(), Error> {
        value.serialize(&mut *self.encoder)
    }

    #[inline]
    fn end(self) -> Result<(), Error> {
        self.end_inner()
    }
}

impl<W: Write> ser::SerializeStruct for CollectionSerializer<'_, W> {
    type Ok = ();
    type Error = Error;

    #[inline]
    fn serialize_field<U: ?Sized + ser::Serialize>(
        &mut self,
        key: &'static str,
        value: &U,
    ) -> Result<(), Error> {
        key.serialize(&mut *self.encoder)?;
        value.serialize(&mut *self.encoder)
    }

    #[inline]
    fn end(self) -> Result<(), Error> {
        self.end_inner()
    }
}

impl<W: Write> ser::SerializeStructVariant for CollectionSerializer<'_, W> {
    type Ok = ();
    type Error = Error;

    #[inline]
    fn serialize_field<U: ?Sized + ser::Serialize>(
        &mut self,
        key: &'static str,
        value: &U,
    ) -> Result<(), Error> {
        key.serialize(&mut *self.encoder)?;
        value.serialize(&mut *self.encoder)
    }

    #[inline]
    fn end(self) -> Result<(), Error> {
        self.end_inner()
    }
}

/// Serializes a value as CBOR into a [`std::io::Write`].
///
/// For repeated small writes consider wrapping the writer in a
/// [`std::io::BufWriter`].
#[inline]
pub fn to_writer<T: ?Sized + ser::Serialize, W: Write>(value: &T, writer: W) -> Result<(), Error> {
    let mut serializer = Serializer::from(writer);
    value.serialize(&mut serializer)
}

/// Serializes a value as CBOR into a new `Vec<u8>`.
#[inline]
pub fn to_vec<T: ?Sized + ser::Serialize>(value: &T) -> Result<Vec<u8>, Error> {
    let mut buffer = Vec::new();
    to_writer(value, &mut buffer)?;
    Ok(buffer)
}

/// Serializes a value as deterministically encoded CBOR into a
/// [`std::io::Write`], satisfying the core deterministic encoding
/// requirements of RFC 8949 §4.2.1.
///
/// This is [`to_canonical_writer_with`] using [`KeyOrder::Bytewise`].
pub fn to_canonical_writer<T: ?Sized + ser::Serialize, W: Write>(
    value: &T,
    writer: W,
) -> Result<(), Error> {
    to_canonical_writer_with(value, writer, KeyOrder::Bytewise)
}

/// Serializes a value as deterministically encoded CBOR into a new
/// `Vec<u8>`, satisfying the core deterministic encoding requirements of
/// RFC 8949 §4.2.1.
///
/// This is [`to_canonical_vec_with`] using [`KeyOrder::Bytewise`].
pub fn to_canonical_vec<T: ?Sized + ser::Serialize>(value: &T) -> Result<Vec<u8>, Error> {
    to_canonical_vec_with(value, KeyOrder::Bytewise)
}

/// Serializes a value as deterministically encoded CBOR into a
/// [`std::io::Write`], sorting map keys in the given [`KeyOrder`].
///
/// See [`Value::canonicalize_with`](crate::Value::canonicalize_with) for
/// the exact normalization rules. The value is buffered as a
/// [`Value`](crate::Value) in order to sort map keys, so this is more
/// expensive than [`to_writer`].
///
/// Maps with duplicate keys (after normalization) are rejected.
pub fn to_canonical_writer_with<T: ?Sized + ser::Serialize, W: Write>(
    value: &T,
    writer: W,
    order: KeyOrder,
) -> Result<(), Error> {
    let mut value = crate::value::Value::serialized(value)?;
    value.canonicalize_with(order)?;
    to_writer(&value, writer)
}

/// Serializes a value as deterministically encoded CBOR into a new
/// `Vec<u8>`, sorting map keys in the given [`KeyOrder`].
///
/// See [`to_canonical_writer_with`] for details.
pub fn to_canonical_vec_with<T: ?Sized + ser::Serialize>(
    value: &T,
    order: KeyOrder,
) -> Result<Vec<u8>, Error> {
    let mut buffer = Vec::new();
    to_canonical_writer_with(value, &mut buffer, order)?;
    Ok(buffer)
}
