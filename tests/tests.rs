extern crate cbor;
extern crate quickcheck;
extern crate rand;
extern crate rustc_serialize;

use std::collections::HashMap;
use std::fmt::Debug;
use rand::thread_rng;
use rustc_serialize::{Decodable, Encodable};
use quickcheck::{QuickCheck, StdGen, Testable};

use cbor::{Encoder, Decoder, Cbor, CborBytes, CborTagEncode};

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
#[should_panic]
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
            CborTagEncode::new(self.num, &self.data).encode(e)
        }
    }
    fn prop(num: u64, data: Vec<i32>) -> bool {
        round_trip(MyTag { num: num, data: data })
    }
    QuickCheck::new().quickcheck(prop as fn(u64, Vec<i32>) -> bool)
}

#[test]
fn roundtrip_tag_fancier_data() {
    use rustc_serialize::{Decoder, Encoder};

    #[derive(Debug, PartialEq, RustcDecodable, RustcEncodable)]
    struct DataName(Vec<u8>);

    #[derive(Debug, PartialEq)]
    struct CustomData {
        name: DataName,
        value: Vec<u8>,
    }

    impl Decodable for CustomData {
        fn decode<D: Decoder>(d: &mut D) -> Result<CustomData, D::Error> {
            let _ = try!(d.read_u64());
            let (name, value) = try!(Decodable::decode(d));
            Ok(CustomData { name: name, value: value })
        }
    }
    impl Encodable for CustomData {
        fn encode<E: Encoder>(&self, e: &mut E) -> Result<(), E::Error> {
            CborTagEncode::new(100_000, &(&self.name, &self.value)).encode(e)
        }
    }
    assert!(round_trip(CustomData {
        name: DataName(b"hello".to_vec()),
        value: vec![1, 2, 3, 4, 5],
    }));
}

#[test]
fn rpc_decode() {
    #[derive(RustcDecodable, RustcEncodable)]
    struct Message {
        id: i64,
        method: String,
        params: CborBytes,
    }

    let send = encode(Message {
        id: 123,
        method: "foobar".to_owned(),
        params: CborBytes(encode(("val".to_owned(), true, -5,))),
    });
    let msg: Message = decode(&send);

    assert_eq!(msg.method, "foobar");
    let (val1, val2, val3): (String, bool, i32) = decode(&msg.params.0);
    assert_eq!(val1, "val");
    assert_eq!(val2, true);
    assert_eq!(val3, -5);
}

#[test]
fn test_oom() {
   let bad = vec![155u8, 0x00, 0xFF, 0xFF, 0xFF, 0x00, 0xFF, 0xFF, 0xFF];
   let mut dec = Decoder::from_bytes(bad);
   assert!(dec.decode::<Vec<u32>>().next().unwrap().is_err());
}

// #[test]
// fn test_oom_direct() {
//   let bad = vec![155u8, 0x00, 0xFF, 0xFF, 0xFF, 0x00, 0xFF, 0xFF, 0xFF];
//   assert!(Vec::<u32>::decode(&mut DirectDecoder::from_bytes(bad)).is_err());
// }

#[test]
fn return_error_on_incomplete_read() {
    // regression test: https://github.com/BurntSushi/rust-cbor/issues/6
    let buf = encode("hello");
    let mut dec = Decoder::from_bytes(&buf[0..4]);
    assert!(dec.decode::<String>().next().unwrap().is_err());
}

/// Test for issue #8
#[test]
fn test_tagged_struct_encoding() {
    use rustc_serialize::Encoder;

    struct MyDataStructure {
        pub data: u64,
    }

    impl Encodable for MyDataStructure {
        fn encode<E: Encoder>(&self, e: &mut E) -> Result<(), E::Error> {
            CborTagEncode::new(43, &self.data).encode(e)
        }
    }

    let mut e = ::cbor::Encoder::from_memory();
    e.encode(&[MyDataStructure {data: 42}]).unwrap();
    assert_eq!(e.as_bytes(), [216, 43, 24, 42]);
}

#[test]
fn validate_indefinite_arrays() {
    let cases = vec![
        (vec![],
         vec![ 0x9f, 0xff,  ]),
        (vec![vec![0]],
         vec![ 0x9f, 0x9f, 0x00, 0xff, 0xff,  ]),
        (vec![vec![0,1],vec![2,3]],
         vec![ 0x9f, 0x9f, 0x00, 0x01, 0xff, 0x9f, 0x02, 0x03, 0xff, 0xff ]),
        (vec![vec![0,1,2],vec![3,4,5],vec![6,7,8]],
         vec![ 0x9f, 0x9f, 0x00, 0x01, 0x02, 0xff, 0x9f, 0x03,
               0x04, 0x05, 0xff, 0x9f, 0x06, 0x07, 0x08, 0xff,
               0xff ]),
    ];
    for (expect, buf) in cases {
        let mut dec = Decoder::from_bytes(buf);
        assert_eq!(dec.decode::<Vec<Vec<u8>>>().next().unwrap().unwrap(),
                   expect);
    }
}

#[test]
fn validate_example_indefinite_bytes() {
    let cases = vec![
        // 2 chunks (with unicode)
        ("exampleα≤β", vec![0x5fu8, 0x47, 101, 120, 97, 109, 112, 108,
                            101, 0x47, 206, 177, 226, 137, 164, 206,
                            178, 0xff]),
        // 1 chunk
        ("example", vec![0x5fu8, 0x47, 101, 120, 97, 109, 112, 108,
                         101, 0xff]),
        // 0 chunks
        ("", vec![0x5fu8, 0xff]),
        // empty chunk
        ("", vec![0x5fu8, 0x40, 0xff]), ];
    for (str, buf) in cases {
        let mut dec = Decoder::from_bytes(buf);
        assert_eq!(dec.decode::<Vec<u8>>().next().unwrap().unwrap(),
                   str.as_bytes());
    }
}

#[test]
fn validate_example_indefinite_string() {
    let cases = vec![
        // 2 chunks (with unicode)
        ("exampleα≤β", vec![0x7fu8, 0x67, 101, 120, 97, 109, 112, 108,
                            101, 0x67, 206, 177, 226, 137, 164, 206,
                            178, 0xff]),
        // 1 chunk
        ("example", vec![0x7fu8, 0x67, 101, 120, 97, 109, 112, 108,
                         101, 0xff]),
        // 0 chunks
        ("", vec![0x7fu8, 0xff]),
        // empty chunk
        ("", vec![0x7fu8, 0x60, 0xff]), ];
    for (str, buf) in cases {
        let mut dec = Decoder::from_bytes(buf);
        assert!(dec.decode::<String>().next().unwrap().unwrap() == str);
    }
}