/*!
This crate provides an implementation of [RFC
7049](https://tools.ietf.org/html/rfc7049), which specifies Concise Binary
Object Representation (CBOR). CBOR adopts and modestly builds on the *data
model* used by JSON, except the encoding is in binary form. Its primary goals
include a balance of implementation size, message size and extensibility.

The implementation here is mostly complete. It includes a mechanism for
serializing and deserializing your own tags, but it does not yet support
indefinite length encoding.

This library is primarily used with type-based encoding and decoding via the
`rustc-serialize` infrastructure, but the raw CBOR abstract syntax is exposed
for use cases that call for it.

# Example: simple type based encoding and decoding

In this crate, there is a `Decoder` and an `Encoder`. All reading and writing
of CBOR must go through one of these types.

The following shows how use those types to encode and decode a sequence of data
items:

```rust
# fn s(x: &str) -> String { x.to_string() }
use cbor::{Decoder, Encoder};

// The data we want to encode. Each element in the list is encoded as its own
// separate top-level data item.
let data = vec![(s("a"), 1), (s("b"), 2), (s("c"), 3)];

// Create an in memory encoder. Use `Encoder::from_writer` to write to anything
// that implements `Writer`.
let mut e = Encoder::from_memory();
e.encode(&data).unwrap();

// Create an in memory decoder. Use `Decoder::from_reader` to read from
// anything that implements `Reader`.
let mut d = Decoder::from_bytes(e.as_bytes());
let items: Vec<(String, i32)> = d.decode().collect::<Result<_, _>>().unwrap();

assert_eq!(items, data);
```

# Example: encode and decode custom tags

This example shows how to encode and decode a custom data type as a CBOR
tag:

```rust
# extern crate rustc_serialize;
# extern crate cbor;
# fn main() {
use cbor::CborTagEncode;
use rustc_serialize::{Decodable, Decoder, Encodable, Encoder};

struct MyDataStructure {
    data: Vec<u32>,
}

impl Encodable for MyDataStructure {
    fn encode<E: Encoder>(&self, e: &mut E) -> Result<(), E::Error> {
        // See a list of tags here:
        // http://www.iana.org/assignments/cbor-tags/cbor-tags.xhtml
        //
        // It is OK to choose your own tag number, but it's probably
        // best to choose one that is unassigned in the IANA registry.
        CborTagEncode::new(100_000, &self.data).encode(e)
    }
}

// Note that the special type `CborTagEncode` isn't needed when decoding. You
// can decode into your `MyDataStructure` type directly:
impl Decodable for MyDataStructure {
    fn decode<D: Decoder>(d: &mut D) -> Result<MyDataStructure, D::Error> {
        // Read the tag number and throw it away. YOU MUST DO THIS!
        try!(d.read_u64());
        // The *next* data item is the actual data.
        Ok(MyDataStructure { data: try!(Decodable::decode(d)) })
    }
}
# }
```

Any value with type `MyDataStructure` can now be used the encoding and
decoding methods used in the first example.

# Example: convert to JSON

Converting to JSON is simple because `Cbor` implements the `ToJson` trait:

```rust
# extern crate rustc_serialize;
# extern crate cbor;
# fn main() {
# fn s(x: &str) -> String { x.to_string() }
use cbor::{Decoder, Encoder};
use rustc_serialize::json::{Json, ToJson};

let mut e = Encoder::from_memory();
e.encode(&[vec![(true, (), 1), (false, (), 2)]]).unwrap();

let mut d = Decoder::from_bytes(e.as_bytes());
let cbor = d.items().next().unwrap().unwrap();

assert_eq!(cbor.to_json(), Json::Array(vec![
    Json::Array(vec![Json::Boolean(true), Json::Null, Json::U64(1)]),
    Json::Array(vec![Json::Boolean(false), Json::Null, Json::U64(2)]),
]));
# }
```

This crate also defines a `ToCbor` trait and implements it for the `Json` type,
so you can convert JSON to CBOR in a similar manner as above.
*/
#![crate_name = "cbor"]
#![doc(html_root_url = "http://burntsushi.net/rustdoc/cbor")]
#![deny(missing_docs)]

#![feature(custom_derive, plugin)]
#![plugin(serde_macros)]

extern crate byteorder;
extern crate rustc_serialize;
extern crate serde;

use std::collections::HashMap;
use std::error::Error;
use std::fmt;
use std::io;

use rustc_serialize::Decoder as RustcDecoder;
use rustc_serialize::Encoder as RustcEncoder;
use rustc_serialize::{Decodable, Encodable};
use serde::{Serialize, Deserialize, ser};

pub use decoder::{DecodedItems, Decoder, Items};
pub use encoder::Encoder;
pub use json::ToCbor;
use rustc_decoder::CborDecoder;
pub use rustc_decoder_direct::CborDecoder as DirectDecoder;
pub use serializer::Serializer;
pub use deserializer::Deserializer;

// A trivial logging macro. No reason to pull in `log`, which has become
// difficult to use in tests.
macro_rules! lg {
    ($($arg:tt)*) => ({
        use std::io::{Write, stderr};
        writeln!(&mut stderr(), $($arg)*).unwrap();
    });
}

macro_rules! fromerr {
    ($e:expr) => ($e.map_err(::std::convert::From::from));
}

/// All core types defined in the CBOR specification.
///
/// For the most part, this is used for convenient error reporting.
#[allow(missing_docs)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Type {
    UInt, UInt8, UInt16, UInt32, UInt64,
    Int, Int8, Int16, Int32, Int64,
    Float, Float16, Float32, Float64,
    Bytes, Unicode, Array, Map, Tag,
    Any, Null, Undefined, Bool, Break,
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl Type {
    fn from_desc(b: u8) -> ReadResult<Type> {
        Ok(match ((b & 0b111_00000) >> 5, b & 0b000_11111) {
            (0, 0...23) => Type::UInt8,
            (0, 24) => Type::UInt8,
            (0, 25) => Type::UInt16,
            (0, 26) => Type::UInt32,
            (0, 27) => Type::UInt64,
            (1, 0...23) => Type::Int8,
            (1, 24) => Type::Int8,
            (1, 25) => Type::Int16,
            (1, 26) => Type::Int32,
            (1, 27) => Type::Int64,
            (2, _) => Type::Bytes,
            (3, _) => Type::Unicode,
            (4, _) => Type::Array,
            (5, _) => Type::Map,
            (6, _) => Type::Tag,
            (7, v @ 0...19) => return Err(ReadError::Unassigned {
                major: 7, add: v,
            }),
            (7, 20...21) => Type::Bool,
            (7, 22) => Type::Null,
            (7, 23) => Type::Undefined,
            (7, 25) => Type::Float16,
            (7, 26) => Type::Float32,
            (7, 27) => Type::Float64,
            (7, v @ 28...30) => return Err(ReadError::Unassigned {
                major: 7, add: v,
            }),
            (7, 31) => Type::Break,
            (x, y) => return Err(ReadError::Unassigned {
                major: x, add: y,
            }),
        })
    }

    fn major(self) -> u8 {
        match self {
            Type::UInt | Type::UInt8 | Type::UInt16
            | Type::UInt32 | Type::UInt64 => 0,
            Type::Int | Type::Int8 | Type::Int16
            | Type::Int32 | Type::Int64 => 1,
            Type::Bytes => 2,
            Type::Unicode => 3,
            Type::Array => 4,
            Type::Map => 5,
            Type::Tag => 6,
            Type::Float | Type::Float16 | Type::Float32 | Type::Float64 => 7,
            Type::Null | Type::Undefined | Type::Bool | Type::Break => 7,
            Type::Any => unreachable!(),
        }
    }
}

/// CBOR abstract syntax.
///
/// This type can represent any data item described in the CBOR specification
/// with some restrictions. Namely, CBOR maps are limited to Unicode string
/// keys.
///
/// Note that this representation distinguishes the size of an encoded number.
#[derive(Clone, Debug, PartialEq)]
pub enum Cbor {
    /// A code used to signify the end of an indefinite length data item.
    Break, // does this really belong here?
    /// An undefined data item (major type 7, value 23).
    Undefined,
    /// A null data item (major type 7, value 22).
    Null,
    /// A boolean data item (major type 7, values 20 or 21).
    Bool(bool),
    /// An unsigned integer (major type 0).
    Unsigned(CborUnsigned),
    /// A negative integer (major type 1).
    Signed(CborSigned),
    /// An IEEE 754 floating point number (major type 7).
    Float(CborFloat),
    /// A byte string (major type 2).
    Bytes(CborBytes),
    /// A Unicode string (major type 3).
    Unicode(String),
    /// An array (major type 4).
    Array(Vec<Cbor>),
    /// A map (major type 5).
    Map(HashMap<String, Cbor>),
    /// A tag (major type 6).
    Tag(CborTag),
}

/// An unsigned integer (major type 0).
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd, RustcDecodable)]
pub enum CborUnsigned {
    /// Unsigned 8 bit integer.
    UInt8(u8),
    /// Unsigned 16 bit integer.
    UInt16(u16),
    /// Unsigned 32 bit integer.
    UInt32(u32),
    /// Unsigned 64 bit integer.
    UInt64(u64)
}

/// A negative integer (major type 1).
///
/// Note that while the number `-255` can be encoded using two bytes as a
/// CBOR `uint8`, it is outside the range of numbers allowed in `i8`.
/// Therefore, when CBOR data is decoded, `-225` is stored as in `i16` in
/// memory.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd, RustcDecodable)]
pub enum CborSigned {
    /// Negative 8 bit integer.
    Int8(i8),
    /// Negative 16 bit integer.
    Int16(i16),
    /// Negative 32 bit integer.
    Int32(i32),
    /// Negative 64 bit integer.
    Int64(i64),
}

/// An IEEE 754 floating point number (major type 7).
#[derive(Clone, Copy, Debug, PartialEq, PartialOrd, RustcDecodable)]
pub enum CborFloat {
    /// IEEE 754 half-precision float.
    ///
    /// *WARNING*: This may be broken right now. ---AG
    Float16(f32),
    /// IEEE 754 single-precision float.
    Float32(f32),
    /// IEEE 754 double-precision float.
    Float64(f64),
}

/// A byte string (major type 2).
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, RustcEncodable)]
pub struct CborBytes(pub Vec<u8>);

/// A tag (major type 6).
///
/// Note that if you want to *encode* a tag, you should use the `CborTagEncode`
/// type and *not* this type. This type is only useful when your manually
/// expecting the structure of a CBOR data item.
#[derive(Clone, Debug, PartialEq, RustcEncodable)]
pub struct CborTag {
    /// The tag number.
    ///
    /// You can see a list of currently assigned tag numbers here:
    /// http://www.iana.org/assignments/cbor-tags/cbor-tags.xhtml
    ///
    /// Note that it is OK to choose your own tag number for your own
    /// application specific purpose, but it should probably be one that is
    /// currently unassigned in the IANA registry.
    pub tag: u64,

    /// The data item, represented in terms of CBOR abstract syntax.
    pub data: Box<Cbor>,
}

impl Serialize for CborTag {
    fn serialize<S>(&self, serializer: &mut S) -> Result<(), S::Error>
        where S: ser::Serializer
    {
        struct Visitor<'a> {
            state: usize,
            value: &'a CborTag,
        }

        impl <'a> ser::MapVisitor for Visitor<'a> {
            #[inline]
            fn visit<S>(&mut self, serializer: &mut S) -> Result<Option<()>, S::Error>
                where S: ser::Serializer
            {
                match self.state {
                    0 => {
                        self.state += 1;
                        Ok(Some(try!(serializer.visit_struct_elt("tag", &self.value.tag))))
                    }
                    1 => {
                        self.state += 1;
                        Ok(Some(try!(serializer.visit_struct_elt("data", &self.value.data))))
                    }
                    _ => Ok(None),
                }
            }
            #[inline]
            fn len(&self) -> Option<usize> { Some(2) }
        }

        serializer.visit_struct("CborTag", Visitor {
            value: self,
            state: 0,
        })
    }
}

/// A special type that can be used to encode CBOR tags.
///
/// This is a "special" type because its used is hard-coded into the
/// implementation of the encoder. When encoded, the encoder will make sure
/// that it is properly represented as a CBOR tag.
///
/// # Example
///
/// This example shows how to encode and decode a custom data type as a CBOR
/// tag:
///
///
/// ```rust
/// # extern crate rustc_serialize;
/// # extern crate cbor;
/// # fn main() {
/// use cbor::CborTagEncode;
/// use rustc_serialize::{Decodable, Decoder, Encodable, Encoder};
///
/// struct MyDataStructure {
///     data: Vec<u32>,
/// }
///
/// impl Encodable for MyDataStructure {
///     fn encode<E: Encoder>(&self, e: &mut E) -> Result<(), E::Error> {
///         // See a list of tags here:
///         // http://www.iana.org/assignments/cbor-tags/cbor-tags.xhtml
///         //
///         // It is OK to choose your own tag number, but it's probably
///         // best to choose one that is unassigned in the IANA registry.
///         CborTagEncode::new(100_000, &self.data).encode(e)
///     }
/// }
///
/// // Note that the special type `CborTagEncode` isn't needed when decoding.
/// // You can decode into your `MyDataStructure` type directly:
/// impl Decodable for MyDataStructure {
///     fn decode<D: Decoder>(d: &mut D) -> Result<MyDataStructure, D::Error> {
///         // Read the tag number and throw it away. YOU MUST DO THIS!
///         try!(d.read_u64());
///         // The *next* data item is the actual data.
///         Ok(MyDataStructure { data: try!(Decodable::decode(d)) })
///     }
/// }
/// # }
/// ```
#[derive(Clone, Debug, PartialEq, RustcEncodable)]
pub struct CborTagEncode<'a, T: 'a> {
    /// The tag number.
    ///
    /// You can see a list of currently assigned tag numbers here:
    /// http://www.iana.org/assignments/cbor-tags/cbor-tags.xhtml
    ///
    /// Note that it is OK to choose your own tag number for your own
    /// application specific purpose, but it should probably be one that is
    /// currently unassigned in the IANA registry.
    __cbor_tag_encode_tag: u64,

    /// The actual data item to encode.
    __cbor_tag_encode_data: &'a T,
}

impl<'a, T> CborTagEncode<'a, T> {
    /// Create a new value that is encodable as a CBOR tag.
    ///
    /// You can see a list of currently assigned tag numbers here:
    /// http://www.iana.org/assignments/cbor-tags/cbor-tags.xhtml
    ///
    /// Note that it is OK to choose your own tag number for your own
    /// application specific purpose, but it should probably be one that is
    /// currently unassigned in the IANA registry.
    ///
    /// `tag` is the tag number and `data` is the actual data item to encode.
    pub fn new(tag: u64, data: &'a T) -> CborTagEncode<'a, T> {
        CborTagEncode {
            __cbor_tag_encode_tag: tag,
            __cbor_tag_encode_data: data,
        }
    }
}

impl<'a, T> Serialize for CborTagEncode<'a, T>
    where T: Serialize,
{
    fn serialize<S>(&self, serializer: &mut S) -> Result<(), S::Error>
        where S: ser::Serializer
    {
        struct Visitor<'a, T: 'a> {
            state: usize,
            value: &'a CborTagEncode<'a, T>,
        }

        impl<'a, T> ser::MapVisitor for Visitor<'a, T>
            where T: Serialize,
        {
            #[inline]
            fn visit<S>(&mut self, serializer: &mut S) -> Result<Option<()>, S::Error>
                where S: ser::Serializer
            {
                match self.state {
                    0 => {
                        self.state += 1;
                        Ok(Some(try!(serializer.visit_struct_elt(
                            "__cbor_tag_encode_tag",
                            &self.value.__cbor_tag_encode_tag))))
                    }
                    1 => {
                        self.state += 1;
                        Ok(Some(try!(serializer.visit_struct_elt(
                            "__cbor_tag_encode_data",
                            &self.value.__cbor_tag_encode_data))))
                    }
                    _ => Ok(None),
                }
            }
            #[inline]
            fn len(&self) -> Option<usize> { Some(2) }
        }

        serializer.visit_struct("CborTagEncode", Visitor {
            value: self,
            state: 0,
        })
    }
}

impl Cbor {
    /// Decode a single CBOR value.
    pub fn decode<D: Decodable>(self) -> CborResult<D> {
        Decodable::decode(&mut CborDecoder::new(self))
    }

    /// If this is a CBOR tag, return the tag number.
    pub fn tag(&self) -> Option<u64> {
        match *self {
            Cbor::Tag(CborTag { tag, .. }) => Some(tag),
            _ => None,
        }
    }

    fn typ(&self) -> Type {
        match *self {
            Cbor::Break => Type::Break,
            Cbor::Undefined => Type::Undefined,
            Cbor::Null => Type::Null,
            Cbor::Bool(_) => Type::Bool,
            Cbor::Unsigned(v) => v.typ(),
            Cbor::Signed(v) => v.typ(),
            Cbor::Float(v) => v.typ(),
            Cbor::Bytes(_) => Type::Bytes,
            Cbor::Unicode(_) => Type::Unicode,
            Cbor::Array(_) => Type::Array,
            Cbor::Map(_) => Type::Map,
            Cbor::Tag(_) => Type::Tag,
        }
    }
}

impl CborUnsigned {
    /// Return the underlying value as a `u64`.
    pub fn into_u64(self) -> u64 {
        self.to_u64().unwrap()
    }

    fn typ(self) -> Type {
        match self {
            CborUnsigned::UInt8(_) => Type::UInt8,
            CborUnsigned::UInt16(_) => Type::UInt16,
            CborUnsigned::UInt32(_) => Type::UInt32,
            CborUnsigned::UInt64(_) => Type::UInt64,
        }
    }

    fn to_usize(self) -> ReadResult<usize> {
        // It should be possible for this to fail. e.g., Converting a
        // UInt64 to a usize when usize is 32 bits.
        Ok(match self {
            CborUnsigned::UInt8(v) => v as usize,
            CborUnsigned::UInt16(v) => v as usize,
            CborUnsigned::UInt32(v) => v as usize,
            CborUnsigned::UInt64(v) => v as usize,
        })
    }

    fn to_u64(self) -> ReadResult<u64> {
        // I don't think this can fail, but it's convenient for it to have
        // the same return type as all of the other integer conversions. ---AG
        Ok(match self {
            CborUnsigned::UInt8(v) => v as u64,
            CborUnsigned::UInt16(v) => v as u64,
            CborUnsigned::UInt32(v) => v as u64,
            CborUnsigned::UInt64(v) => v,
        })
    }

    fn to_u32(self) -> ReadResult<u32> {
        Ok(match self {
            CborUnsigned::UInt8(v) => v as u32,
            CborUnsigned::UInt16(v) => v as u32,
            CborUnsigned::UInt32(v) => v,
            _ => return Err(ReadError::ty_mismatch(Type::UInt32, self.typ())),
        })
    }

    fn to_u16(self) -> ReadResult<u16> {
        Ok(match self {
            CborUnsigned::UInt8(v) => v as u16,
            CborUnsigned::UInt16(v) => v,
            _ => return Err(ReadError::ty_mismatch(Type::UInt16, self.typ())),
        })
    }

    fn to_u8(self) -> ReadResult<u8> {
        Ok(match self {
            CborUnsigned::UInt8(v) => v,
            _ => return Err(ReadError::ty_mismatch(Type::UInt8, self.typ())),
        })
    }
}

impl CborSigned {
    /// Return the underlying value as a `i64`.
    pub fn into_i64(self) -> i64 {
        self.to_i64().unwrap()
    }

    fn typ(self) -> Type {
        match self {
            CborSigned::Int8(_) => Type::Int8,
            CborSigned::Int16(_) => Type::Int16,
            CborSigned::Int32(_) => Type::Int32,
            CborSigned::Int64(_) => Type::Int64,
        }
    }

    fn to_isize(self) -> ReadResult<isize> {
        // It should be possible for this to fail. e.g., Converting a
        // UInt64 to a usize when usize is 32 bits.
        Ok(match self {
            CborSigned::Int8(v) => v as isize,
            CborSigned::Int16(v) => v as isize,
            CborSigned::Int32(v) => v as isize,
            CborSigned::Int64(v) => v as isize,
        })
    }

    fn to_i64(self) -> ReadResult<i64> {
        // I don't think this can fail, but it's convenient for it to have
        // the same return type as all of the other integer conversions. ---AG
        Ok(match self {
            CborSigned::Int8(v) => v as i64,
            CborSigned::Int16(v) => v as i64,
            CborSigned::Int32(v) => v as i64,
            CborSigned::Int64(v) => v,
        })
    }

    fn to_i32(self) -> ReadResult<i32> {
        Ok(match self {
            CborSigned::Int8(v) => v as i32,
            CborSigned::Int16(v) => v as i32,
            CborSigned::Int32(v) => v,
            _ => return Err(ReadError::ty_mismatch(Type::Int32, self.typ())),
        })
    }

    fn to_i16(self) -> ReadResult<i16> {
        Ok(match self {
            CborSigned::Int8(v) => v as i16,
            CborSigned::Int16(v) => v,
            _ => return Err(ReadError::ty_mismatch(Type::Int16, self.typ())),
        })
    }

    fn to_i8(self) -> ReadResult<i8> {
        Ok(match self {
            CborSigned::Int8(v) => v,
            _ => return Err(ReadError::ty_mismatch(Type::Int8, self.typ())),
        })
    }
}

impl CborFloat {
    /// Return the underlying value as a `f64`.
    pub fn into_f64(self) -> f64 {
        self.to_f64().unwrap()
    }

    fn typ(self) -> Type {
        match self {
            CborFloat::Float16(_) => Type::Float16,
            CborFloat::Float32(_) => Type::Float32,
            CborFloat::Float64(_) => Type::Float64,
        }
    }

    fn to_f64(self) -> ReadResult<f64> {
        // I don't think this can fail, but it's convenient for it to have
        // the same return type as all of the other number conversions. ---AG
        Ok(match self {
            CborFloat::Float16(v) => v as f64,
            CborFloat::Float32(v) => v as f64,
            CborFloat::Float64(v) => v,
        })
    }

    fn to_f32(self) -> ReadResult<f32> {
        Ok(match self {
            CborFloat::Float16(v) => v,
            CborFloat::Float32(v) => v,
            _ => return Err(ReadError::ty_mismatch(Type::Float32, self.typ())),
        })
    }
}

impl Encodable for Cbor {
    fn encode<E: RustcEncoder>(&self, e: &mut E) -> Result<(), E::Error> {
        match *self {
            // Not sure what to do with `Break` here. I guess if we need to
            // be able to encode, we'll have to add special support for it
            // in the encoder.
            Cbor::Break => unimplemented!(),
            Cbor::Undefined => e.emit_nil(),
            Cbor::Null => e.emit_nil(),
            Cbor::Bool(v) => v.encode(e),
            Cbor::Unsigned(v) => v.encode(e),
            Cbor::Signed(v) => v.encode(e),
            Cbor::Float(v) => v.encode(e),
            Cbor::Bytes(ref v) => v.encode(e),
            Cbor::Unicode(ref v) => v.encode(e),
            Cbor::Array(ref v) => v.encode(e),
            Cbor::Map(ref v) => v.encode(e),
            Cbor::Tag(ref v) => v.encode(e),
        }
    }
}

impl Encodable for CborUnsigned {
    fn encode<E: RustcEncoder>(&self, e: &mut E) -> Result<(), E::Error> {
        match *self {
            CborUnsigned::UInt8(v) => v.encode(e),
            CborUnsigned::UInt16(v) => v.encode(e),
            CborUnsigned::UInt32(v) => v.encode(e),
            CborUnsigned::UInt64(v) => v.encode(e),
        }
    }
}

impl Encodable for CborSigned {
    fn encode<E: RustcEncoder>(&self, e: &mut E) -> Result<(), E::Error> {
        match *self {
            CborSigned::Int8(v) => v.encode(e),
            CborSigned::Int16(v) => v.encode(e),
            CborSigned::Int32(v) => v.encode(e),
            CborSigned::Int64(v) => v.encode(e),
        }
    }
}

impl Encodable for CborFloat {
    fn encode<E: RustcEncoder>(&self, e: &mut E) -> Result<(), E::Error> {
        match *self {
            CborFloat::Float16(v) => v.encode(e),
            CborFloat::Float32(v) => v.encode(e),
            CborFloat::Float64(v) => v.encode(e),
        }
    }
}

impl ::std::ops::Deref for CborBytes {
    type Target = [u8];

    fn deref(&self) -> &[u8] { &self.0 }
}

impl ::std::ops::DerefMut for CborBytes {
    fn deref_mut(&mut self) -> &mut [u8] { &mut self.0 }
}

impl Decodable for CborBytes {
    fn decode<D: RustcDecoder>(d: &mut D) -> Result<CborBytes, D::Error> {
        Decodable::decode(d).map(CborBytes)
    }
}

impl Serialize for CborBytes {
    fn serialize<S>(&self, serializer: &mut S) -> Result<(), S::Error>
        where S: serde::Serializer,
    {
        serializer.visit_bytes(self)
    }
}

impl Deserialize for CborBytes {
    fn deserialize<D>(deserializer: &mut D) -> Result<CborBytes, D::Error>
        where D: serde::Deserializer,
    {
        let value: serde::bytes::ByteBuf = try!(Deserialize::deserialize(deserializer));
        Ok(CborBytes(value.into()))
    }
}


impl Serialize for Cbor {
    fn serialize<S>(&self, serializer: &mut S) -> Result<(), S::Error>
        where S: serde::ser::Serializer,
    {
        match *self {
            // Not sure what to do with `Break` here. I guess if we need to
            // be able to encode, we'll have to add special support for it
            // in the encoder.
            Cbor::Break => unimplemented!(),
            Cbor::Undefined => serializer.visit_unit(),
            Cbor::Null => serializer.visit_unit(),
            Cbor::Bool(v) => v.serialize(serializer),
            Cbor::Unsigned(v) => v.serialize(serializer),
            Cbor::Signed(v) => v.serialize(serializer),
            Cbor::Float(v) => v.serialize(serializer),
            Cbor::Bytes(ref v) => v.serialize(serializer),
            Cbor::Unicode(ref v) => v.serialize(serializer),
            Cbor::Array(ref v) => v.serialize(serializer),
            Cbor::Map(ref v) => v.serialize(serializer),
            Cbor::Tag(ref v) => v.serialize(serializer),
        }
    }
}

impl Serialize for CborUnsigned {
    fn serialize<S>(&self, serializer: &mut S) -> Result<(), S::Error>
        where S: serde::Serializer,
    {
        match *self {
            CborUnsigned::UInt8(v) => v.serialize(serializer),
            CborUnsigned::UInt16(v) => v.serialize(serializer),
            CborUnsigned::UInt32(v) => v.serialize(serializer),
            CborUnsigned::UInt64(v) => v.serialize(serializer),
        }
    }
}

impl Serialize for CborSigned {
    fn serialize<S>(&self, serializer: &mut S) -> Result<(), S::Error>
        where S: serde::Serializer,
    {
        match *self {
            CborSigned::Int8(v) => v.serialize(serializer),
            CborSigned::Int16(v) => v.serialize(serializer),
            CborSigned::Int32(v) => v.serialize(serializer),
            CborSigned::Int64(v) => v.serialize(serializer),
        }
    }
}

impl Serialize for CborFloat {
    fn serialize<S>(&self, serializer: &mut S) -> Result<(), S::Error>
        where S: serde::Serializer,
    {
        match *self {
            CborFloat::Float16(v) => v.serialize(serializer),
            CborFloat::Float32(v) => v.serialize(serializer),
            CborFloat::Float64(v) => v.serialize(serializer),
        }
    }
}


/// Type synonym for `Result<T, CborError>`.
pub type CborResult<T> = Result<T, CborError>;

/// Type synonym for `Result<T, ReadError>`.
type ReadResult<T> = Result<T, ReadError>;

/// Errors that can be produced by a CBOR operation.
#[derive(Debug)]
pub enum CborError {
    /// An error as a result of an  underlying IO operation.
    Io(io::Error),
    /// An error from the type based decoder.
    Decode(ReadError), // decoder loses byte offset information :-(
    /// An error from the type based encoder.
    Encode(WriteError),
    /// An error reading CBOR at a particular offset.
    ///
    /// For example, if the data in "additional information" is inconsistent
    /// with the major type.
    AtOffset {
        /// The exact read error.
        kind: ReadError,
        /// The byte offset at which the error occurred.
        offset: usize,
    },
    /// EOF is found but more bytes were expected to decode the next data item.
    ///
    /// EOF is triggered when the underlying reader returns `0` bytes.
    UnexpectedEOF,
}

impl serde::de::Error for CborError {
    fn syntax(msg: &str) -> Self {
        CborError::Decode(ReadError::Other(format!("syntax error: {}", msg)))
    }

    fn end_of_stream() -> Self {
        CborError::UnexpectedEOF
    }

    fn unknown_field(field: &str) -> Self {
        CborError::Decode(ReadError::Other(format!("unknown field: {}", field)))
    }

    fn missing_field(field: &'static str) -> Self {
        CborError::Decode(ReadError::Other(format!("missing field: {}", field)))
    }
}

impl CborError {
    fn is_eof(&self) -> bool {
        match *self {
            CborError::UnexpectedEOF => true,
            _ => false,
        }
    }
}

/// An error produced by reading CBOR data.
#[derive(Clone, Debug)]
pub enum ReadError {
    /// An error for when the expected type does not match the received type.
    TypeMismatch {
        /// Expected CBOR type.
        expected: Type,
        /// Received CBOR type.
        got: Type,
    },
    /// When the additional information is inconsistent with the major type.
    InvalidAddValue {
        /// CBOR type.
        ty: Type,
        /// Additional information value.
        val: u8,
    },
    /// The value found is unassigned.
    Unassigned {
        /// CBOR major type value.
        major: u8,
        /// Additional information value.
        add: u8,
    },
    /// The value found is reserved.
    Reserved {
        /// CBOR major type value.
        major: u8,
        /// Additional information value.
        add: u8,
    },
    /// Some other error occurred.
    Other(String),
}

/// An error produced by writing CBOR data.
#[derive(Clone, Debug)]
pub enum WriteError {
    /// Occurs when writing a map key that isn't a Unicode string.
    InvalidMapKey {
        /// The received type (if that information is available).
        got: Option<Type>,
    },
}

impl From<io::Error> for CborError {
    fn from(err: io::Error) -> CborError { CborError::Io(err) }
}

impl From<byteorder::Error> for CborError {
    fn from(err: byteorder::Error) -> CborError {
        match err {
            byteorder::Error::UnexpectedEOF => CborError::UnexpectedEOF,
            byteorder::Error::Io(err) => From::from(err),
        }
    }
}

impl Error for CborError {
    fn description(&self) -> &str {
        use CborError::*;
        match *self {
            Io(ref err) => err.description(),
            Decode(_) => "decode error",
            Encode(_) => "encode error",
            AtOffset { .. } => "read error",
            UnexpectedEOF => "unexpected EOF",
        }
    }

    fn cause(&self) -> Option<&Error> {
        match *self {
            CborError::Io(ref err) => err.cause(),
            _ => None,
        }
    }
}

impl ReadError {
    fn mismatch(expected: Type, got: &Cbor) -> ReadError {
        ReadError::ty_mismatch(expected, got.typ())
    }

    fn ty_mismatch(expected: Type, got: Type) -> ReadError {
        ReadError::TypeMismatch { expected: expected, got: got }
    }

    fn miss(expected: Type, got: u8) -> ReadError {
        let ty = match Type::from_desc(got) {
            Ok(ty) => ty,
            Err(err) => return err,
        };
        ReadError::TypeMismatch { expected: expected, got: ty }
    }
}

impl fmt::Display for CborError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            CborError::Io(ref err) => write!(f, "{}", err),
            CborError::Decode(ref err) => {
                write!(f, "Error while decoding: {}", err)
            }
            CborError::Encode(ref err) => {
                write!(f, "Error while encoding: {}", err)
            }
            CborError::AtOffset { ref kind, offset } => {
                write!(f, "Error at byte offset {:?}: {}", offset, kind)
            }
            CborError::UnexpectedEOF => write!(f, "Unexpected EOF."),
        }
    }
}

impl fmt::Display for ReadError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ReadError::TypeMismatch { expected, got } => {
                write!(f, "Expected type {:?}, but found {:?}.", expected, got)
            }
            ReadError::InvalidAddValue { ty, val } => {
                write!(f, "Invalid additional information ({:?}) \
                           for type {:?}", val, ty)
            }
            ReadError::Unassigned { major, add } => {
                write!(f, "Found unassigned value (major type: {:?}, \
                           additional information: {:?})", major, add)
            }
            ReadError::Reserved { major, add } => {
                write!(f, "Found reserved value (major type: {:?}, \
                           additional information: {:?})", major, add)
            }
            ReadError::Other(ref s) => write!(f, "{}", s),
        }
    }
}

impl fmt::Display for WriteError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            WriteError::InvalidMapKey { got: Some(got) } => {
                write!(f, "Found invalid map key ({:?}), \
                           expected Unicode string.", got)
            }
            WriteError::InvalidMapKey { got: None } => {
                write!(f, "Found invalid map key, expected Unicode string.")
            }
        }
    }
}

mod decoder;
mod encoder;
mod json;
mod rustc_decoder;
mod rustc_decoder_direct;
mod serializer;
mod deserializer;

/// Encode a CBOR value into a Vec<u8>.
pub fn encode<T: Encodable>(v: T) -> Vec<u8> {
    let mut ser = Encoder::from_memory();
    ser.encode(&[v]).unwrap();
    ser.as_bytes().to_vec()
}

/// Encode a CBOR value into a writer.
pub fn encode_into<W: io::Write, T: Encodable>(wr: W, v: T) -> CborResult<()> {
    let mut ser = Encoder::from_writer(wr);
    ser.encode(&[v])
}

/// Decode a CBOR value from a `&[u8]`.
pub fn decode<T: Decodable>(bytes: &[u8]) -> CborResult<T> {
    Decoder::from_bytes(bytes).decode().next().unwrap()
}

/// Decode a CBOR value from a reader.
pub fn decode_from<R: io::Read, T: Decodable>(rdr: R) -> CborResult<T> {
    Decoder::from_reader(rdr).decode().next().unwrap()
}

/// Serialize a CBOR value into a Vec<u8>.
pub fn serialize<T: Serialize>(v: T) -> Vec<u8> {
    let mut ser = Serializer::from_memory();
    ser.serialize(&[v]).unwrap();
    ser.as_bytes().to_vec()
}

/// Serialize a CBOR value into a writer.
pub fn serialize_into<W: io::Write, T: Serialize>(wr: W, v: T) -> CborResult<()> {
    let mut ser = Serializer::from_writer(wr);
    ser.serialize(&[v])
}

/// Deserialize a CBOR value from a `&[u8]`.
pub fn deserialize<T: Deserialize>(bytes: &[u8]) -> CborResult<T> {
    Deserialize::deserialize(&mut Deserializer::from_bytes(bytes))
}

/// Deserialize a CBOR value from a reader.
pub fn deserialize_from<R: io::Read, T: Deserialize>(rdr: R) -> CborResult<T> {
    Deserialize::deserialize(&mut Deserializer::from_reader(rdr))
}
