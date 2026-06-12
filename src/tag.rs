//! Helper types for capturing and emitting CBOR tags (RFC 8949 §3.4).
//!
//! Serde has no native notion of a CBOR tag. These wrapper types smuggle the
//! tag number through serde's data model using an internal protocol that the
//! serializers and deserializers in this crate understand:
//!
//! ```rust
//! use cbor::tag::RequireExact;
//!
//! // Tag 0: a date/time string.
//! let datetime = RequireExact::<_, 0>("2013-03-21T20:04:00Z".to_string());
//!
//! let bytes = cbor::to_vec(&datetime).unwrap();
//! assert_eq!(hex::decode("c074323031332d30332d32315432303a30343a30305a").unwrap(), bytes);
//!
//! let back: RequireExact<String, 0> = cbor::from_slice(&bytes).unwrap();
//! assert_eq!(back, datetime);
//! ```
//!
//! Note that these types are only meaningful with the CBOR serializer and
//! deserializer from this crate; other formats will see the internal
//! protocol.

use serde::{de, forward_to_deserialize_any, ser, Deserialize, Serialize};

// The internal tag protocol: an enum with a magic name whose variants the
// CBOR serializer and deserializer special-case. This is wire-compatible
// with the `ciborium` crate.
pub(crate) const NAME: &str = "@@TAG@@";
pub(crate) const UNTAGGED: &str = "@@UNTAGGED@@";
pub(crate) const TAGGED: &str = "@@TAGGED@@";

enum Internal<T> {
    Untagged(T),
    Tagged(u64, T),
}

impl<T: Serialize> Serialize for Internal<&T> {
    fn serialize<S: ser::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeTupleVariant;

        match self {
            Internal::Untagged(value) => {
                serializer.serialize_newtype_variant(NAME, 0, UNTAGGED, value)
            }
            Internal::Tagged(tag, value) => {
                let mut acc = serializer.serialize_tuple_variant(NAME, 1, TAGGED, 2)?;
                acc.serialize_field(tag)?;
                acc.serialize_field(value)?;
                acc.end()
            }
        }
    }
}

impl<'de, T: Deserialize<'de>> Deserialize<'de> for Internal<T> {
    fn deserialize<D: de::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        enum Variant {
            Untagged,
            Tagged,
        }

        struct VariantVisitor;

        impl de::Visitor<'_> for VariantVisitor {
            type Value = Variant;

            fn expecting(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                write!(f, "a tag variant identifier")
            }

            fn visit_u64<E: de::Error>(self, value: u64) -> Result<Variant, E> {
                match value {
                    0 => Ok(Variant::Untagged),
                    1 => Ok(Variant::Tagged),
                    x => Err(de::Error::invalid_value(
                        de::Unexpected::Unsigned(x),
                        &"variant index 0 or 1",
                    )),
                }
            }

            fn visit_str<E: de::Error>(self, value: &str) -> Result<Variant, E> {
                match value {
                    UNTAGGED => Ok(Variant::Untagged),
                    TAGGED => Ok(Variant::Tagged),
                    x => Err(de::Error::unknown_variant(x, &[UNTAGGED, TAGGED])),
                }
            }
        }

        impl<'de> Deserialize<'de> for Variant {
            fn deserialize<D: de::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
                deserializer.deserialize_identifier(VariantVisitor)
            }
        }

        struct TaggedVisitor<T>(core::marker::PhantomData<T>);

        impl<'de, T: Deserialize<'de>> de::Visitor<'de> for TaggedVisitor<T> {
            type Value = (u64, T);

            fn expecting(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                write!(f, "a tag number and a value")
            }

            fn visit_seq<A: de::SeqAccess<'de>>(self, mut acc: A) -> Result<Self::Value, A::Error> {
                let tag = acc
                    .next_element()?
                    .ok_or_else(|| de::Error::invalid_length(0, &self))?;
                let val = acc
                    .next_element()?
                    .ok_or_else(|| de::Error::invalid_length(1, &self))?;
                Ok((tag, val))
            }
        }

        struct InternalVisitor<T>(core::marker::PhantomData<T>);

        impl<'de, T: Deserialize<'de>> de::Visitor<'de> for InternalVisitor<T> {
            type Value = Internal<T>;

            fn expecting(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                write!(f, "a possibly tagged value")
            }

            fn visit_enum<A: de::EnumAccess<'de>>(self, acc: A) -> Result<Self::Value, A::Error> {
                use de::VariantAccess;

                match acc.variant()? {
                    (Variant::Untagged, access) => {
                        Ok(Internal::Untagged(access.newtype_variant()?))
                    }
                    (Variant::Tagged, access) => {
                        let (tag, val) =
                            access.tuple_variant(2, TaggedVisitor(core::marker::PhantomData))?;
                        Ok(Internal::Tagged(tag, val))
                    }
                }
            }
        }

        deserializer.deserialize_enum(
            NAME,
            &[UNTAGGED, TAGGED],
            InternalVisitor(core::marker::PhantomData),
        )
    }
}

/// Allows any tag, or no tag at all.
///
/// The tag (if present) is captured during deserialization and emitted
/// during serialization.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AllowAny<V>(pub Option<u64>, pub V);

impl<'de, V: Deserialize<'de>> Deserialize<'de> for AllowAny<V> {
    #[inline]
    fn deserialize<D: de::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match Internal::deserialize(deserializer)? {
            Internal::Tagged(t, v) => Ok(AllowAny(Some(t), v)),
            Internal::Untagged(v) => Ok(AllowAny(None, v)),
        }
    }
}

impl<V: Serialize> Serialize for AllowAny<V> {
    #[inline]
    fn serialize<S: ser::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self.0 {
            Some(tag) => Internal::Tagged(tag, &self.1).serialize(serializer),
            None => Internal::Untagged(&self.1).serialize(serializer),
        }
    }
}

/// Allows a specific tag, or no tag at all.
///
/// The tag is always emitted during serialization.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AllowExact<V, const TAG: u64>(pub V);

impl<'de, V: Deserialize<'de>, const TAG: u64> Deserialize<'de> for AllowExact<V, TAG> {
    #[inline]
    fn deserialize<D: de::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match Internal::deserialize(deserializer)? {
            Internal::Tagged(t, v) if t == TAG => Ok(AllowExact(v)),
            Internal::Untagged(v) => Ok(AllowExact(v)),
            _ => Err(de::Error::custom("unexpected tag")),
        }
    }
}

impl<V: Serialize, const TAG: u64> Serialize for AllowExact<V, TAG> {
    #[inline]
    fn serialize<S: ser::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        Internal::Tagged(TAG, &self.0).serialize(serializer)
    }
}

/// Requires a tag with any number to be present.
///
/// The tag is always emitted during serialization.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RequireAny<V>(pub u64, pub V);

impl<'de, V: Deserialize<'de>> Deserialize<'de> for RequireAny<V> {
    #[inline]
    fn deserialize<D: de::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match Internal::deserialize(deserializer)? {
            Internal::Tagged(t, v) => Ok(RequireAny(t, v)),
            _ => Err(de::Error::custom("required tag not found")),
        }
    }
}

impl<V: Serialize> Serialize for RequireAny<V> {
    #[inline]
    fn serialize<S: ser::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        Internal::Tagged(self.0, &self.1).serialize(serializer)
    }
}

/// Requires a specific tag to be present.
///
/// The tag is always emitted during serialization.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RequireExact<V, const TAG: u64>(pub V);

impl<'de, V: Deserialize<'de>, const TAG: u64> Deserialize<'de> for RequireExact<V, TAG> {
    #[inline]
    fn deserialize<D: de::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match Internal::deserialize(deserializer)? {
            Internal::Tagged(t, v) if t == TAG => Ok(RequireExact(v)),
            _ => Err(de::Error::custom("required tag not found")),
        }
    }
}

impl<V: Serialize, const TAG: u64> Serialize for RequireExact<V, TAG> {
    #[inline]
    fn serialize<S: ser::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        Internal::Tagged(TAG, &self.0).serialize(serializer)
    }
}

// An `EnumAccess`/`Deserializer` that presents a tagged item to a visitor
// using the internal tag protocol. The parent deserializer provides the
// item following the tag.
pub(crate) struct TagAccess<D> {
    parent: Option<D>,
    state: usize,
    tag: Option<u64>,
}

impl<D> TagAccess<D> {
    pub(crate) fn new(parent: D, tag: Option<u64>) -> Self {
        Self {
            parent: Some(parent),
            state: 0,
            tag,
        }
    }
}

impl<'de, D: de::Deserializer<'de>> de::Deserializer<'de> for &mut TagAccess<D> {
    type Error = D::Error;

    #[inline]
    fn deserialize_any<V: de::Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        self.state += 1;

        match self.state {
            1 => visitor.visit_str(match self.tag {
                Some(..) => TAGGED,
                None => UNTAGGED,
            }),

            _ => visitor.visit_u64(self.tag.unwrap()),
        }
    }

    forward_to_deserialize_any! {
        i8 i16 i32 i64 i128
        u8 u16 u32 u64 u128
        bool f32 f64
        char str string
        bytes byte_buf
        seq map
        struct tuple tuple_struct
        identifier ignored_any
        option unit unit_struct newtype_struct enum
    }
}

impl<'de, D: de::Deserializer<'de>> de::EnumAccess<'de> for TagAccess<D> {
    type Error = D::Error;
    type Variant = Self;

    #[inline]
    fn variant_seed<V: de::DeserializeSeed<'de>>(
        mut self,
        seed: V,
    ) -> Result<(V::Value, Self::Variant), Self::Error> {
        let variant = seed.deserialize(&mut self)?;
        Ok((variant, self))
    }
}

impl<'de, D: de::Deserializer<'de>> de::VariantAccess<'de> for TagAccess<D> {
    type Error = D::Error;

    #[inline]
    fn unit_variant(self) -> Result<(), Self::Error> {
        Err(de::Error::custom("expected tag"))
    }

    #[inline]
    fn newtype_variant_seed<U: de::DeserializeSeed<'de>>(
        mut self,
        seed: U,
    ) -> Result<U::Value, Self::Error> {
        seed.deserialize(self.parent.take().unwrap())
    }

    #[inline]
    fn tuple_variant<V: de::Visitor<'de>>(
        self,
        _len: usize,
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        visitor.visit_seq(self)
    }

    #[inline]
    fn struct_variant<V: de::Visitor<'de>>(
        self,
        _fields: &'static [&'static str],
        _visitor: V,
    ) -> Result<V::Value, Self::Error> {
        Err(de::Error::custom("expected tag"))
    }
}

impl<'de, D: de::Deserializer<'de>> de::SeqAccess<'de> for TagAccess<D> {
    type Error = D::Error;

    #[inline]
    fn next_element_seed<T: de::DeserializeSeed<'de>>(
        &mut self,
        seed: T,
    ) -> Result<Option<T::Value>, Self::Error> {
        if self.state < 2 {
            return Ok(Some(seed.deserialize(&mut *self)?));
        }

        Ok(match self.parent.take() {
            Some(x) => Some(seed.deserialize(x)?),
            None => None,
        })
    }
}

// The serializer used to extract a tag number from the first field of the
// tag pseudo-variant. Every other input is an error.
#[derive(Debug)]
pub(crate) struct NotATag;

impl core::fmt::Display for NotATag {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "expected tag")
    }
}

impl ser::StdError for NotATag {}

impl ser::Error for NotATag {
    fn custom<U: core::fmt::Display>(_msg: U) -> Self {
        NotATag
    }
}

pub(crate) struct TagNumberSerializer;

impl ser::Serializer for TagNumberSerializer {
    type Ok = u64;
    type Error = NotATag;

    type SerializeSeq = ser::Impossible<u64, NotATag>;
    type SerializeTuple = ser::Impossible<u64, NotATag>;
    type SerializeTupleStruct = ser::Impossible<u64, NotATag>;
    type SerializeTupleVariant = ser::Impossible<u64, NotATag>;
    type SerializeMap = ser::Impossible<u64, NotATag>;
    type SerializeStruct = ser::Impossible<u64, NotATag>;
    type SerializeStructVariant = ser::Impossible<u64, NotATag>;

    #[inline]
    fn serialize_u8(self, v: u8) -> Result<u64, NotATag> {
        Ok(v.into())
    }

    #[inline]
    fn serialize_u16(self, v: u16) -> Result<u64, NotATag> {
        Ok(v.into())
    }

    #[inline]
    fn serialize_u32(self, v: u32) -> Result<u64, NotATag> {
        Ok(v.into())
    }

    #[inline]
    fn serialize_u64(self, v: u64) -> Result<u64, NotATag> {
        Ok(v)
    }

    fn serialize_bool(self, _: bool) -> Result<u64, NotATag> {
        Err(NotATag)
    }

    fn serialize_i8(self, _: i8) -> Result<u64, NotATag> {
        Err(NotATag)
    }

    fn serialize_i16(self, _: i16) -> Result<u64, NotATag> {
        Err(NotATag)
    }

    fn serialize_i32(self, _: i32) -> Result<u64, NotATag> {
        Err(NotATag)
    }

    fn serialize_i64(self, _: i64) -> Result<u64, NotATag> {
        Err(NotATag)
    }

    fn serialize_i128(self, _: i128) -> Result<u64, NotATag> {
        Err(NotATag)
    }

    fn serialize_u128(self, _: u128) -> Result<u64, NotATag> {
        Err(NotATag)
    }

    fn serialize_f32(self, _: f32) -> Result<u64, NotATag> {
        Err(NotATag)
    }

    fn serialize_f64(self, _: f64) -> Result<u64, NotATag> {
        Err(NotATag)
    }

    fn serialize_char(self, _: char) -> Result<u64, NotATag> {
        Err(NotATag)
    }

    fn serialize_str(self, _: &str) -> Result<u64, NotATag> {
        Err(NotATag)
    }

    fn serialize_bytes(self, _: &[u8]) -> Result<u64, NotATag> {
        Err(NotATag)
    }

    fn serialize_none(self) -> Result<u64, NotATag> {
        Err(NotATag)
    }

    fn serialize_some<U: ?Sized + ser::Serialize>(self, _: &U) -> Result<u64, NotATag> {
        Err(NotATag)
    }

    fn serialize_unit(self) -> Result<u64, NotATag> {
        Err(NotATag)
    }

    fn serialize_unit_struct(self, _: &'static str) -> Result<u64, NotATag> {
        Err(NotATag)
    }

    fn serialize_unit_variant(
        self,
        _: &'static str,
        _: u32,
        _: &'static str,
    ) -> Result<u64, NotATag> {
        Err(NotATag)
    }

    fn serialize_newtype_struct<U: ?Sized + ser::Serialize>(
        self,
        _: &'static str,
        _: &U,
    ) -> Result<u64, NotATag> {
        Err(NotATag)
    }

    fn serialize_newtype_variant<U: ?Sized + ser::Serialize>(
        self,
        _: &'static str,
        _: u32,
        _: &'static str,
        _: &U,
    ) -> Result<u64, NotATag> {
        Err(NotATag)
    }

    fn serialize_seq(self, _: Option<usize>) -> Result<Self::SerializeSeq, NotATag> {
        Err(NotATag)
    }

    fn serialize_tuple(self, _: usize) -> Result<Self::SerializeTuple, NotATag> {
        Err(NotATag)
    }

    fn serialize_tuple_struct(
        self,
        _: &'static str,
        _: usize,
    ) -> Result<Self::SerializeTupleStruct, NotATag> {
        Err(NotATag)
    }

    fn serialize_tuple_variant(
        self,
        _: &'static str,
        _: u32,
        _: &'static str,
        _: usize,
    ) -> Result<Self::SerializeTupleVariant, NotATag> {
        Err(NotATag)
    }

    fn serialize_map(self, _: Option<usize>) -> Result<Self::SerializeMap, NotATag> {
        Err(NotATag)
    }

    fn serialize_struct(self, _: &'static str, _: usize) -> Result<Self::SerializeStruct, NotATag> {
        Err(NotATag)
    }

    fn serialize_struct_variant(
        self,
        _: &'static str,
        _: u32,
        _: &'static str,
        _: usize,
    ) -> Result<Self::SerializeStructVariant, NotATag> {
        Err(NotATag)
    }

    fn is_human_readable(&self) -> bool {
        false
    }
}
