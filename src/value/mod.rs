//! A dynamic CBOR value.

mod canonical;
mod de;
mod integer;
mod ser;

pub use canonical::KeyOrder;
pub use integer::Integer;

/// An error when serializing to or deserializing from a [`Value`].
#[derive(Clone, Debug)]
pub enum Error {
    /// A custom error message produced by serde.
    Custom(String),
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Error::Custom(msg) => write!(f, "{msg}"),
        }
    }
}

impl std::error::Error for Error {}

impl serde::de::Error for Error {
    #[inline]
    fn custom<T: core::fmt::Display>(msg: T) -> Self {
        Self::Custom(msg.to_string())
    }
}

impl serde::ser::Error for Error {
    #[inline]
    fn custom<T: core::fmt::Display>(msg: T) -> Self {
        Self::Custom(msg.to_string())
    }
}

/// A representation of any CBOR item that can be inspected and manipulated
/// dynamically.
///
/// Maps are represented as `Vec<(Value, Value)>` rather than as an ordered
/// or hashed map type. This preserves the order of the pairs on the wire and
/// makes no assumptions about key uniqueness; `collect()` the pairs into a
/// map type of your choice if you need one.
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub enum Value {
    /// An integer (major type 0 or 1).
    Integer(Integer),

    /// A byte string (major type 2).
    Bytes(Vec<u8>),

    /// A floating-point value (major type 7).
    Float(f64),

    /// A text string (major type 3).
    Text(String),

    /// A boolean (major type 7).
    Bool(bool),

    /// Null (major type 7).
    Null,

    /// A tagged value (major type 6).
    Tag(u64, Box<Value>),

    /// An array (major type 4).
    Array(Vec<Value>),

    /// A map (major type 5).
    Map(Vec<(Value, Value)>),
}

macro_rules! accessors {
    ($(#[doc = $doc:literal] $is:ident $as:ident $into:ident($variant:ident) -> $t:ty;)+) => {
        $(
            #[doc = concat!("Returns true if the value is ", $doc, ".")]
            #[inline]
            pub fn $is(&self) -> bool {
                matches!(self, Value::$variant(..))
            }

            #[doc = concat!("If the value is ", $doc, ", returns a reference to it. Returns `None` otherwise.")]
            #[inline]
            pub fn $as(&self) -> Option<&$t> {
                match self {
                    Value::$variant(x) => Some(x),
                    _ => None,
                }
            }

            #[doc = concat!("If the value is ", $doc, ", returns it as `Ok`. Returns `Err(self)` otherwise.")]
            #[inline]
            pub fn $into(self) -> Result<$t, Self> {
                match self {
                    Value::$variant(x) => Ok(x),
                    other => Err(other),
                }
            }
        )+
    };
}

impl Value {
    accessors! {
        #[doc = "a byte string"]
        is_bytes as_bytes into_bytes(Bytes) -> Vec<u8>;

        #[doc = "an array"]
        is_array as_array into_array(Array) -> Vec<Value>;

        #[doc = "a map"]
        is_map as_map into_map(Map) -> Vec<(Value, Value)>;
    }

    /// Returns true if the value is an integer.
    #[inline]
    pub fn is_integer(&self) -> bool {
        matches!(self, Value::Integer(..))
    }

    /// If the value is an integer, returns it. Returns `None` otherwise.
    #[inline]
    pub fn as_integer(&self) -> Option<Integer> {
        match self {
            Value::Integer(x) => Some(*x),
            _ => None,
        }
    }

    /// If the value is an integer, returns it as `Ok`. Returns `Err(self)`
    /// otherwise.
    #[inline]
    pub fn into_integer(self) -> Result<Integer, Self> {
        match self {
            Value::Integer(x) => Ok(x),
            other => Err(other),
        }
    }

    /// Returns true if the value is a float.
    #[inline]
    pub fn is_float(&self) -> bool {
        matches!(self, Value::Float(..))
    }

    /// If the value is a float, returns it. Returns `None` otherwise.
    #[inline]
    pub fn as_float(&self) -> Option<f64> {
        match self {
            Value::Float(x) => Some(*x),
            _ => None,
        }
    }

    /// If the value is a float, returns it as `Ok`. Returns `Err(self)`
    /// otherwise.
    #[inline]
    pub fn into_float(self) -> Result<f64, Self> {
        match self {
            Value::Float(x) => Ok(x),
            other => Err(other),
        }
    }

    /// Returns true if the value is a text string.
    #[inline]
    pub fn is_text(&self) -> bool {
        matches!(self, Value::Text(..))
    }

    /// If the value is a text string, returns a reference to it. Returns
    /// `None` otherwise.
    #[inline]
    pub fn as_text(&self) -> Option<&str> {
        match self {
            Value::Text(x) => Some(x),
            _ => None,
        }
    }

    /// If the value is a text string, returns it as `Ok`. Returns
    /// `Err(self)` otherwise.
    #[inline]
    pub fn into_text(self) -> Result<String, Self> {
        match self {
            Value::Text(x) => Ok(x),
            other => Err(other),
        }
    }

    /// Returns true if the value is a boolean.
    #[inline]
    pub fn is_bool(&self) -> bool {
        matches!(self, Value::Bool(..))
    }

    /// If the value is a boolean, returns it. Returns `None` otherwise.
    #[inline]
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Value::Bool(x) => Some(*x),
            _ => None,
        }
    }

    /// If the value is a boolean, returns it as `Ok`. Returns `Err(self)`
    /// otherwise.
    #[inline]
    pub fn into_bool(self) -> Result<bool, Self> {
        match self {
            Value::Bool(x) => Ok(x),
            other => Err(other),
        }
    }

    /// Returns true if the value is null.
    #[inline]
    pub fn is_null(&self) -> bool {
        matches!(self, Value::Null)
    }

    /// Returns true if the value is a tag.
    #[inline]
    pub fn is_tag(&self) -> bool {
        matches!(self, Value::Tag(..))
    }

    /// If the value is a tag, returns the tag number and a reference to the
    /// inner value. Returns `None` otherwise.
    #[inline]
    pub fn as_tag(&self) -> Option<(u64, &Value)> {
        match self {
            Value::Tag(tag, data) => Some((*tag, data)),
            _ => None,
        }
    }

    /// If the value is a tag, returns the pair of the tag number and the
    /// inner value as `Ok`. Returns `Err(self)` otherwise.
    #[inline]
    pub fn into_tag(self) -> Result<(u64, Box<Value>), Self> {
        match self {
            Value::Tag(tag, data) => Ok((tag, data)),
            other => Err(other),
        }
    }

    /// If the value is a byte string, returns a mutable reference to it.
    /// Returns `None` otherwise.
    #[inline]
    pub fn as_bytes_mut(&mut self) -> Option<&mut Vec<u8>> {
        match self {
            Value::Bytes(x) => Some(x),
            _ => None,
        }
    }

    /// If the value is a text string, returns a mutable reference to it.
    /// Returns `None` otherwise.
    #[inline]
    pub fn as_text_mut(&mut self) -> Option<&mut String> {
        match self {
            Value::Text(x) => Some(x),
            _ => None,
        }
    }

    /// If the value is an array, returns a mutable reference to it. Returns
    /// `None` otherwise.
    #[inline]
    pub fn as_array_mut(&mut self) -> Option<&mut Vec<Value>> {
        match self {
            Value::Array(x) => Some(x),
            _ => None,
        }
    }

    /// If the value is a map, returns a mutable reference to it. Returns
    /// `None` otherwise.
    #[inline]
    pub fn as_map_mut(&mut self) -> Option<&mut Vec<(Value, Value)>> {
        match self {
            Value::Map(x) => Some(x),
            _ => None,
        }
    }

    /// If the value is a tag, returns mutable references to the tag number
    /// and the inner value. Returns `None` otherwise.
    #[inline]
    pub fn as_tag_mut(&mut self) -> Option<(&mut u64, &mut Value)> {
        match self {
            Value::Tag(tag, data) => Some((tag, data.as_mut())),
            _ => None,
        }
    }
}

macro_rules! implfrom {
    ($($variant:ident($t:ty)),+ $(,)?) => {
        $(
            impl From<$t> for Value {
                #[inline]
                fn from(value: $t) -> Self {
                    Self::$variant(value.into())
                }
            }
        )+
    };
}

implfrom! {
    Integer(Integer),
    Integer(u64),
    Integer(i64),
    Integer(u32),
    Integer(i32),
    Integer(u16),
    Integer(i16),
    Integer(u8),
    Integer(i8),

    Bytes(Vec<u8>),
    Bytes(&[u8]),

    Float(f64),
    Float(f32),

    Text(String),
    Text(&str),

    Bool(bool),

    Array(&[Value]),
    Array(Vec<Value>),

    Map(&[(Value, Value)]),
    Map(Vec<(Value, Value)>),
}

impl From<u128> for Value {
    #[inline]
    fn from(value: u128) -> Self {
        if let Ok(x) = Integer::try_from(value) {
            return Value::Integer(x);
        }

        let mut bytes = &value.to_be_bytes()[..];
        while let Some(0) = bytes.first() {
            bytes = &bytes[1..];
        }

        Value::Tag(crate::core::tag::BIGPOS, Value::Bytes(bytes.into()).into())
    }
}

impl From<i128> for Value {
    #[inline]
    fn from(value: i128) -> Self {
        if let Ok(x) = Integer::try_from(value) {
            return Value::Integer(x);
        }

        let (tag, raw) = match value.is_negative() {
            true => (crate::core::tag::BIGNEG, value as u128 ^ !0),
            false => (crate::core::tag::BIGPOS, value as u128),
        };

        let mut bytes = &raw.to_be_bytes()[..];
        while let Some(0) = bytes.first() {
            bytes = &bytes[1..];
        }

        Value::Tag(tag, Value::Bytes(bytes.into()).into())
    }
}

impl From<char> for Value {
    #[inline]
    fn from(value: char) -> Self {
        let mut v = String::with_capacity(value.len_utf8());
        v.push(value);
        Value::Text(v)
    }
}
