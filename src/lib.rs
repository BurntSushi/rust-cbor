#![crate_name = "cbor"]
#![doc(html_root_url = "http://burntsushi.net/rustdoc/cbor")]

use std::collections::HashMap;

pub enum Cbor {
    Primitive(CborPrimitive),
    Array(Vec<Cbor>),
    Map(HashMap<CborPrimitive, Cbor>),
    Tag(Box<Cbor>),
}

pub enum CborPrimitive {
    Unsigned(CborUnsigned),
    Signed(CborSigned),
    Float(CborFloat),
    Bytes(Vec<u8>),
    Unicode(String),
}

#[derive(Copy)]
pub enum CborUnsigned { UInt8(u8), UInt16(u16), UInt32(u32), UInt64(u64) }
#[derive(Copy)]
pub enum CborSigned { Int8(i8), Int16(i16), Int32(i32), Int64(i64) }
#[derive(Copy)]
pub enum CborFloat { Float32(f32), Float64(f64) }
