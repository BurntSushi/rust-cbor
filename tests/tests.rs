#![allow(unused_features)]
#![feature(io)]

extern crate cbor;
extern crate quickcheck;
extern crate rand;
extern crate "rustc-serialize" as rustc_serialize;

use std::collections::HashMap;
use std::fmt::Debug;
use rand::thread_rng;
use rustc_serialize::{Decodable, Encodable};
use quickcheck::{QuickCheck, StdGen, Testable};

use cbor::{Encoder, Decoder, Cbor, CborBytes, CborTagEncode};

// A trivial logging macro. No reason to pull in `log`, which has become
// difficult to use in tests.
macro_rules! lg {
    ($($arg:tt)*) => ({
        let _ = ::std::old_io::stderr().write_str(&*format!($($arg)*));
        let _ = ::std::old_io::stderr().write_str("\n");
    });
}

fn qc_sized<A: Testable>(f: A, size: u64) {
    QuickCheck::new()
        .gen(StdGen::new(thread_rng(), size as usize))
        .tests(1_00)
        .max_tests(10_000)
        .quickcheck(f);
}

fn round_trip<T>(v: T) -> bool
        where T: Decodable + Encodable + Debug + PartialEq {
    let backv: T = decode(&encode(&v));
    assert_eq!(backv, v);
    true
}

fn encode<T: Encodable>(v: T) -> Vec<u8> {
    let mut enc = Encoder::from_memory();
    enc.encode(&[v]).unwrap();
    enc.as_bytes().to_vec()
}

fn decode<T: Decodable>(bytes: &[u8]) -> T {
    Decoder::from_bytes(bytes).decode().next().unwrap().unwrap()
}

#[allow(dead_code)]
fn readone(bytes: &[u8]) -> Cbor {
    Decoder::from_bytes(bytes).items().next().unwrap().unwrap()
}

macro_rules! round_trip_num {
    ($name:ident, $ty:ident) => (
        #[test]
        fn $name() {
            fn prop(n: $ty) -> bool { round_trip(n) }
            qc_sized(prop as fn($ty) -> bool, ::std::$ty::MAX as u64)
        }
    );
}

round_trip_num!(roundtrip_prop_usize, usize);
round_trip_num!(roundtrip_prop_u64, u64);
round_trip_num!(roundtrip_prop_u32, u32);
round_trip_num!(roundtrip_prop_u16, u16);
round_trip_num!(roundtrip_prop_u8, u8);
round_trip_num!(roundtrip_prop_isize, isize);
round_trip_num!(roundtrip_prop_i64, i64);
round_trip_num!(roundtrip_prop_i32, i32);
round_trip_num!(roundtrip_prop_i16, i16);
round_trip_num!(roundtrip_prop_i8, i8);

#[test]
fn roundtrip_prop_f32() {
    fn prop(n: f32) -> bool { round_trip(n) }
    qc_sized(prop as fn(f32) -> bool, ::std::f32::MAX_VALUE as u64 - 1)
}

#[test]
fn roundtrip_prop_f64() {
    fn prop(n: f64) -> bool { round_trip(n) }
    qc_sized(prop as fn(f64) -> bool, ::std::f64::MAX_VALUE as u64 - 1)
}

macro_rules! round_trip_any {
    ($name:ident, $ty:ty) => (
        #[test]
        fn $name() {
            fn prop(n: $ty) -> bool { round_trip(n) }
            QuickCheck::new().quickcheck(prop as fn($ty) -> bool)
        }
    );
}

round_trip_any!(roundtrip_prop_nil, ());
round_trip_any!(roundtrip_prop_bool, bool);
round_trip_any!(roundtrip_prop_tuple, (i32, u32));
round_trip_any!(roundtrip_prop_tuple_in_tuple, (i32, (u32, i32), u32));
round_trip_any!(roundtrip_prop_vec, Vec<i32>);
round_trip_any!(roundtrip_prop_vec_in_vec, Vec<Vec<i32>>);
round_trip_any!(roundtrip_prop_map, HashMap<String, i32>);
round_trip_any!(roundtrip_prop_vec_in_map, HashMap<String, Vec<i32>>);
// round_trip_any!(roundtrip_prop_map_in_map,
                // HashMap<String, HashMap<String, i32>>);

#[test]
fn roundtrip_prop_byte_string() {
    fn prop(n: Vec<u8>) -> bool { round_trip(CborBytes(n)) }
    QuickCheck::new().quickcheck(prop as fn(Vec<u8>) -> bool)
}

#[test]
fn roundtrip_enum() {
    #[derive(Debug, PartialEq, RustcDecodable, RustcEncodable)]
    enum Color { Red, Blue(String, i32), Green { s: String, n: i32 } }

    round_trip(Color::Red);
    round_trip(Color::Blue("hi".to_string(), 5));
    round_trip(Color::Green { s: "hi".to_string(), n: 5 });
}

#[test]
fn roundtrip_struct() {
    #[derive(Debug, PartialEq, RustcDecodable, RustcEncodable)]
    struct Vowels { s: String, n: u32 }

    round_trip(Vowels { s: "cwm".to_string(), n: 1 });
}

#[test]
#[should_fail]
fn invalid_map_key() {
    let mut map = HashMap::new();
    map.insert(5, 5);
    encode(map);
}

#[test]
fn roundtrip_prop_tag() {
    use rustc_serialize::{Decoder, Encoder};

    #[derive(Debug, PartialEq)]
    struct MyTag {
        num: u64,
        data: Vec<i32>,
    }
    impl Decodable for MyTag {
        fn decode<D: Decoder>(d: &mut D) -> Result<MyTag, D::Error> {
            let tag = try!(d.read_u64());
            Ok(MyTag { num: tag, data: try!(Decodable::decode(d)) })
        }
    }
    impl Encodable for MyTag {
        fn encode<E: Encoder>(&self, e: &mut E) -> Result<(), E::Error> {
            CborTagEncode {
                tag: self.num,
                data: &self.data,
            }.encode(e)
        }
    }
    fn prop(num: u64, data: Vec<i32>) -> bool {
        round_trip(MyTag { num: num, data: data })
    }
    QuickCheck::new().quickcheck(prop as fn(u64, Vec<i32>) -> bool)
}
