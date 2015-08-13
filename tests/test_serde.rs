#![feature(custom_derive, plugin)]
#![plugin(serde_macros)]

extern crate cbor;
extern crate quickcheck;
extern crate rand;
extern crate rustc_serialize;
extern crate serde;

use std::collections::HashMap;
use std::fmt::Debug;
use rand::thread_rng;
use quickcheck::{QuickCheck, StdGen, Testable};
use serde::{ser, de, Deserialize, Serialize};

use cbor::{Serializer, CborBytes, CborTagEncode};

fn qc_sized<A: Testable>(f: A, size: u64) {
    QuickCheck::new()
        .gen(StdGen::new(thread_rng(), size as usize))
        .tests(1_00)
        .max_tests(10_000)
        .quickcheck(f);
}

fn round_trip<T>(v: T) -> bool
        where T: Deserialize + Serialize + Debug + PartialEq {
    let backv: T = cbor::deserialize(&cbor::serialize(&v)).unwrap();
    assert_eq!(backv, v);
    true
}

macro_rules! round_trip_num {
    ($name:ident, $ty:ident) => (
        #[test]
        fn $name() {
            #![allow(trivial_numeric_casts)]
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
    qc_sized(prop as fn(f32) -> bool, ::std::u64::MAX)
}

#[test]
fn roundtrip_prop_f64() {
    fn prop(n: f64) -> bool { round_trip(n) }
    qc_sized(prop as fn(f64) -> bool, ::std::u64::MAX)
}

#[test]
fn roundtrip_f32_min() {
    round_trip(::std::f32::MIN);
}

#[test]
fn roundtrip_f32_max() {
    round_trip(::std::f32::MAX);
}

#[test]
fn roundtrip_f64_min() {
    round_trip(::std::f64::MIN);
}

#[test]
fn roundtrip_f64_max() {
    round_trip(::std::f64::MAX);
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
    #[derive(Debug, PartialEq, Deserialize, Serialize)]
    enum Color { Red, Blue(String, i32), Green { s: String, n: i32 } }

    round_trip(Color::Red);
    round_trip(Color::Blue("hi".to_string(), 5));
    round_trip(Color::Green { s: "hi".to_string(), n: 5 });
}

#[test]
fn roundtrip_struct() {
    #[derive(Debug, PartialEq, Deserialize, Serialize)]
    struct Vowels { s: String, n: u32 }

    round_trip(Vowels { s: "cwm".to_string(), n: 1 });
}

#[test]
#[should_panic]
fn invalid_map_key() {
    let mut map = HashMap::new();
    map.insert(5, 5);
    cbor::serialize(map);
}

#[test]
fn roundtrip_prop_tag() {
    #[derive(Debug, PartialEq)]
    struct MyTag {
        num: u64,
        data: Vec<i32>,
    }
    impl Deserialize for MyTag {
        fn deserialize<D: de::Deserializer>(deserializer: &mut D) -> Result<MyTag, D::Error> {
            let tag = try!(Deserialize::deserialize(deserializer));
            Ok(MyTag {
                num: tag,
                data: try!(Deserialize::deserialize(deserializer)),
            })
        }
    }
    impl Serialize for MyTag {
        fn serialize<S>(&self, serializer: &mut S) -> Result<(), S::Error>
            where S: serde::Serializer,
        {
            CborTagEncode::new(self.num, &self.data).serialize(serializer)
        }
    }
    fn prop(num: u64, data: Vec<i32>) -> bool {
        round_trip(MyTag { num: num, data: data })
    }
    QuickCheck::new().quickcheck(prop as fn(u64, Vec<i32>) -> bool)
}

#[test]
fn roundtrip_tag_fancier_data() {
    #[derive(Debug, PartialEq, Deserialize, Serialize)]
    struct DataName(Vec<u8>);

    #[derive(Debug, PartialEq)]
    struct CustomData {
        name: DataName,
        value: Vec<u8>,
    }

    impl Deserialize for CustomData {
        fn deserialize<D: de::Deserializer>(d: &mut D) -> Result<CustomData, D::Error> {
            let _ = try!(u64::deserialize(d));
            let (name, value) = try!(de::Deserialize::deserialize(d));
            Ok(CustomData { name: name, value: value })
        }
    }
    impl Serialize for CustomData {
        fn serialize<S: ser::Serializer>(&self, s: &mut S) -> Result<(), S::Error> {
            CborTagEncode::new(100_000, &(&self.name, &self.value)).serialize(s)
        }
    }
    assert!(round_trip(CustomData {
        name: DataName(b"hello".to_vec()),
        value: vec![1, 2, 3, 4, 5],
    }));
}

#[test]
fn rpc_decode() {
    #[derive(Deserialize, Serialize)]
    struct Message {
        id: i64,
        method: String,
        params: CborBytes,
    }

    let send = cbor::serialize(Message {
        id: 123,
        method: "foobar".to_owned(),
        params: CborBytes(cbor::serialize(("val".to_owned(), true, -5,))),
    });
    let msg: Message = cbor::deserialize(&send).unwrap();

    assert_eq!(msg.method, "foobar");
    let (val1, val2, val3): (String, bool, i32) = cbor::deserialize(&msg.params.0).unwrap();
    assert_eq!(val1, "val");
    assert_eq!(val2, true);
    assert_eq!(val3, -5);
}

#[test]
fn test_oom() {
   let bad = vec![155u8, 0x00, 0xFF, 0xFF, 0xFF, 0x00, 0xFF, 0xFF, 0xFF];
   let mut dec: cbor::CborResult<Vec<u32>> = cbor::deserialize(&bad);
   assert!(dec.is_err());
}

// #[test]
// fn test_oom_direct() {
   // let bad = vec![155u8, 0x00, 0xFF, 0xFF, 0xFF, 0x00, 0xFF, 0xFF, 0xFF];
   // assert!(Vec::<u32>::decode(&mut DirectDecoder::from_bytes(bad)).is_err());
// }
