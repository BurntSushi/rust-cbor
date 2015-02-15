use rustc_serialize::base64::{STANDARD, ToBase64};
use rustc_serialize::json::{Json, ToJson};

use {Cbor, CborFloat, CborSigned, CborUnsigned};

/// A trait for converting values to CBOR.
pub trait ToCbor {
    /// Return a CBOR representation of `self`.
    fn to_cbor(&self) -> Cbor;
}

impl ToJson for Cbor {
    fn to_json(&self) -> Json {
        match *self {
            Cbor::Break => unimplemented!(),
            Cbor::Undefined => Json::Null,
            Cbor::Null => Json::Null,
            Cbor::Bool(v) => Json::Boolean(v),
            Cbor::Unsigned(v) => Json::U64(v.to_u64().unwrap()),
            Cbor::Signed(v) => Json::I64(v.to_i64().unwrap()),
            Cbor::Float(v) => Json::F64(v.to_f64().unwrap()),
            Cbor::Bytes(ref v) => Json::String(v.to_base64(STANDARD)),
            Cbor::Unicode(ref v) => Json::String(v.clone()),
            Cbor::Array(ref v) => Json::Array(
                v.iter().map(|v| v.to_json()).collect()
            ),
            Cbor::Map(ref v) => Json::Object(
                v.iter().map(|(k, v)| (k.clone(), v.to_json())).collect()
            ),
            Cbor::Tag(ref v) => v.data.to_json(),
        }
    }
}

impl ToCbor for Json {
    fn to_cbor(&self) -> Cbor {
        // TODO: Use the smallest sized number types possible.
        // Maybe factor out some of the code in the encoder? ---AG
        match *self {
            Json::Null => Cbor::Null,
            Json::Boolean(v) => Cbor::Bool(v),
            Json::U64(v) => Cbor::Unsigned(CborUnsigned::UInt64(v)),
            Json::I64(v) => Cbor::Signed(CborSigned::Int64(v)),
            Json::F64(v) => Cbor::Float(CborFloat::Float64(v)),
            Json::String(ref v) => Cbor::Unicode(v.clone()),
            Json::Array(ref v) => Cbor::Array(
                v.iter().map(|v| v.to_cbor()).collect()
            ),
            Json::Object(ref v) => Cbor::Map(
                v.iter().map(|(k, v)| (k.clone(), v.to_cbor())).collect()
            ),
        }
    }
}
