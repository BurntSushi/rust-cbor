#![feature(test)]

extern crate cbor;
extern crate rustc_serialize;
extern crate test;

use std::iter::repeat;
use cbor::{Decoder, DirectDecoder, Encoder};
use rustc_serialize::{Decodable, Encodable};
use rustc_serialize::json::{self, Json, ToJson};

#[bench]
fn encode_small_cbor(b: &mut test::Bencher) {
    let data = ("hello, world".to_string(),
                true, (), vec![1, 1000, 100_000, 10_000_000], 3.14);

    b.bytes = cbor::encode(&data).len() as u64;
    b.iter(|| {
        cbor::encode(&data);
    });
}

#[bench]
fn encode_small_json(b: &mut test::Bencher) {
    let data = ("hello, world".to_string(),
                true, (), vec![1, 1000, 100_000, 10_000_000], 3.14);

    b.bytes = data.to_json().to_string().len() as u64;
    b.iter(|| {
        json::encode(&data).unwrap();
    });
}

#[bench]
fn encode_small_tojson(b: &mut test::Bencher) {
    let data = ("hello, world".to_string(),
                true, (), vec![1, 1000, 100_000, 10_000_000], 3.14);

    b.bytes = data.to_json().to_string().len() as u64;
    b.iter(|| {
        data.to_json().to_string();
    });
}

#[bench]
fn encode_medium_cbor(b: &mut test::Bencher) {
    let data = ("hello, world".to_string(),
                true, (), vec![1, 1000, 100_000, 10_000_000], 3.14);
    let items = repeat(&data).take(10_000).collect::<Vec<_>>();

    b.bytes = cbor::encode(&items).len() as u64;
    b.iter(|| {
        cbor::encode(&items);
    });
}

#[bench]
fn encode_medium_json(b: &mut test::Bencher) {
    let data = ("hello, world".to_string(),
                true, (), vec![1, 1000, 100_000, 10_000_000], 3.14);
    let items = repeat(data).take(10_000).collect::<Vec<_>>();

    b.bytes = items.to_json().to_string().len() as u64;
    b.iter(|| {
        json::encode(&items).unwrap();
    });
}

#[bench]
fn encode_medium_tojson(b: &mut test::Bencher) {
    let data = ("hello, world".to_string(),
                true, (), vec![1, 1000, 100_000, 10_000_000], 3.14);
    let items = repeat(data).take(10_000).collect::<Vec<_>>();

    b.bytes = items.to_json().to_string().len() as u64;
    b.iter(|| {
        items.to_json().to_string();
    });
}

#[bench]
fn read_small_cbor(b: &mut test::Bencher) {
    let data = ("hello, world".to_string(),
                true, (), vec![1, 1000, 100_000, 10_000_000], 3.14);
    let mut enc = Encoder::from_memory();
    enc.encode(&[data]).unwrap();
    let bytes = enc.as_bytes();

    b.bytes = bytes.len() as u64;
    b.iter(|| {
        let mut dec = Decoder::from_bytes(bytes.to_vec());
        dec.items().next().unwrap().unwrap();
    });
}

#[bench]
fn read_small_json(b: &mut test::Bencher) {
    let data = ("hello, world".to_string(),
                true, (), vec![1, 1000, 100_000, 10_000_000], 3.14);
    let string = json::encode(&data).unwrap();

    b.bytes = string.len() as u64;
    b.iter(|| {
        Json::from_str(&string).unwrap();
    });
}

#[bench]
fn read_medium_cbor(b: &mut test::Bencher) {
    let data = ("hello, world".to_string(),
                true, (), vec![1, 1000, 100_000, 10_000_000], 3.14);
    let items = repeat(data).take(10_000).collect::<Vec<_>>();
    let mut enc = Encoder::from_memory();
    enc.encode(&[items]).unwrap();
    let bytes = enc.as_bytes();

    b.bytes = bytes.len() as u64;
    b.iter(|| {
        let mut dec = Decoder::from_bytes(bytes.to_vec());
        dec.items().next().unwrap().unwrap();
    });
}

#[bench]
fn read_medium_json(b: &mut test::Bencher) {
    let data = ("hello, world".to_string(),
                true, (), vec![1, 1000, 100_000, 10_000_000], 3.14);
    let items = repeat(data).take(10_000).collect::<Vec<_>>();
    let string = json::encode(&items).unwrap();

    b.bytes = string.len() as u64;
    b.iter(|| {
        Json::from_str(&string).unwrap();
    });
}

#[bench]
fn decode_small_cbor(b: &mut test::Bencher) {
    let data = ("hello, world".to_string(),
                true, (), vec![1, 1000, 100_000, 10_000_000], 3.14);
    let mut enc = Encoder::from_memory();
    enc.encode(&[data]).unwrap();
    let bytes = enc.as_bytes();

    b.bytes = bytes.len() as u64;
    b.iter(|| {
        let mut dec = Decoder::from_bytes(bytes.to_vec());
        let _: (String, bool, (), Vec<u64>, f64) =
            dec.decode().next().unwrap().unwrap();
    });
}

#[bench]
fn decode_small_direct_cbor(b: &mut test::Bencher) {
    let data = ("hello, world".to_string(),
                true, (), vec![1, 1000, 100_000, 10_000_000], 3.14);
    let mut enc = Encoder::from_memory();
    enc.encode(&[data]).unwrap();
    let bytes = enc.as_bytes();

    b.bytes = bytes.len() as u64;
    b.iter(|| {
        let mut dec = DirectDecoder::from_bytes(bytes.to_vec());
        let _: (String, bool, (), Vec<u64>, f64) =
            Decodable::decode(&mut dec).unwrap();
    });
}

#[bench]
fn decode_small_json(b: &mut test::Bencher) {
    let data = ("hello, world".to_string(),
                true, (), vec![1, 1000, 100_000, 10_000_000], 3.14);
    let string = json::encode(&data).unwrap();

    b.bytes = string.len() as u64;
    b.iter(|| {
        let _: (String, bool, (), Vec<u64>, f64) =
            json::decode(&string).unwrap();
    });
}

#[bench]
fn decode_medium_cbor(b: &mut test::Bencher) {
    let data = ("hello, world".to_string(),
                true, (), vec![1, 1000, 100_000, 10_000_000], 3.14);
    let items = repeat(data).take(10_000).collect::<Vec<_>>();
    let mut enc = Encoder::from_memory();
    enc.encode(&[items]).unwrap();
    let bytes = enc.as_bytes();

    b.bytes = bytes.len() as u64;
    b.iter(|| {
        let mut dec = Decoder::from_bytes(bytes.to_vec());
        let _: Vec<(String, bool, (), Vec<u64>, f64)> =
            dec.decode().next().unwrap().unwrap();
    });
}

#[bench]
fn decode_medium_direct_cbor(b: &mut test::Bencher) {
    let data = ("hello, world".to_string(),
                true, (), vec![1, 1000, 100_000, 10_000_000], 3.14);
    let items = repeat(data).take(10_000).collect::<Vec<_>>();
    let mut enc = Encoder::from_memory();
    enc.encode(&[items]).unwrap();
    let bytes = enc.as_bytes();

    b.bytes = bytes.len() as u64;
    b.iter(|| {
        let mut dec = DirectDecoder::from_bytes(bytes.to_vec());
        let _: Vec<(String, bool, (), Vec<u64>, f64)> =
            Decodable::decode(&mut dec).unwrap();
    });
}

#[bench]
fn decode_medium_json(b: &mut test::Bencher) {
    let data = ("hello, world".to_string(),
                true, (), vec![1, 1000, 100_000, 10_000_000], 3.14);
    let items = repeat(data).take(10_000).collect::<Vec<_>>();
    let string = json::encode(&items).unwrap();

    b.bytes = string.len() as u64;
    b.iter(|| {
        let _: Vec<(String, bool, (), Vec<u64>, f64)> =
            json::decode(&string).unwrap();
    });
}
