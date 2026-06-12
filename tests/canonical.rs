//! Tests for deterministic encoding (RFC 8949 §4.2).

use std::collections::HashMap;

use cbor::{cbor, KeyOrder, Value};

// The eight example keys shared by RFC 8949 §4.2.1 and §4.2.3, scrambled.
fn rfc_example_map() -> Value {
    Value::Map(vec![
        (cbor!([-1]).unwrap(), Value::from(6)),
        (Value::from(false), Value::from(7)),
        (Value::from("aa"), Value::from(4)),
        (Value::from(100), Value::from(1)),
        (Value::from(-1), Value::from(2)),
        (cbor!([100]).unwrap(), Value::from(5)),
        (Value::from(10), Value::from(0)),
        (Value::from("z"), Value::from(3)),
    ])
}

fn keys_of(value: &Value) -> Vec<String> {
    value
        .as_map()
        .unwrap()
        .iter()
        .map(|(k, _)| hex::encode(cbor::to_vec(k).unwrap()))
        .collect()
}

#[test]
fn rfc_key_order_example() {
    // RFC 8949 §4.2.1 (bytewise lexicographic): the keys must come out as
    // 10, 100, -1, "z", "aa", [100], [-1], false.
    let mut value = rfc_example_map();
    value.canonicalize().unwrap();

    assert_eq!(
        keys_of(&value),
        ["0a", "1864", "20", "617a", "626161", "811864", "8120", "f4"]
    );
}

#[test]
fn rfc_key_order_example_length_first() {
    // RFC 8949 §4.2.3 / RFC 7049 §3.9 (length-first): the same keys must
    // come out as 10, -1, false, 100, "z", [-1], "aa", [100].
    let mut value = rfc_example_map();
    value.canonicalize_with(KeyOrder::LengthFirst).unwrap();

    assert_eq!(
        keys_of(&value),
        ["0a", "20", "f4", "1864", "617a", "8120", "626161", "811864"]
    );
}

#[test]
fn length_first_through_serde() {
    let map: HashMap<i64, bool> = [(100, true), (-1, false)].into();

    let core = cbor::to_canonical_vec(&map).unwrap();
    assert_eq!(hex::encode(&core), "a21864f520f4");

    let legacy = cbor::to_canonical_vec_with(&map, KeyOrder::LengthFirst).unwrap();
    assert_eq!(hex::encode(&legacy), "a220f41864f5");

    // Both reject duplicate keys.
    let dup = Value::Map(vec![
        (Value::from(1), Value::Null),
        (Value::from(1), Value::Null),
    ]);
    assert!(cbor::to_canonical_vec_with(&dup, KeyOrder::LengthFirst).is_err());

    // The default order is bytewise.
    assert_eq!(
        core,
        cbor::to_canonical_vec_with(&map, KeyOrder::default()).unwrap()
    );
}

#[test]
fn sorting_recurses() {
    // Nested maps are sorted wherever they appear: in values, in array
    // elements, inside tags and even when used as keys.
    let mut value = cbor!({
        "outer" => { "z" => 1, "aa" => 2 },
        "list" => [{ "z" => 1, "aa" => 2 }],
    })
    .unwrap();
    let mut tagged = Value::Tag(1000, Box::new(value.clone()));

    value.canonicalize().unwrap();
    tagged.canonicalize().unwrap();

    let expect = |v: &Value| {
        let map = v.as_map().unwrap();
        // "list" (0x646c697374) sorts before "outer" (0x656f75746572).
        assert_eq!(map[0].0, Value::from("list"));
        let inner = map[1].1.as_map().unwrap();
        assert_eq!(inner[0].0, Value::from("z"));
        assert_eq!(inner[1].0, Value::from("aa"));
    };

    expect(&value);
    expect(tagged.as_tag().unwrap().1);

    let mut map_key = Value::Map(vec![(value, Value::Null)]);
    map_key.canonicalize().unwrap();
    expect(&map_key.as_map().unwrap()[0].0);
}

#[test]
fn duplicate_keys_are_rejected() {
    let mut value = Value::Map(vec![
        (Value::from(1), Value::from("a")),
        (Value::from(1), Value::from("b")),
    ]);
    assert!(value.canonicalize().is_err());

    // Keys that only become equal after normalization also count: the
    // bignum 2(h'01') is the integer 1.
    let mut value = Value::Map(vec![
        (Value::from(1), Value::from("a")),
        (
            Value::Tag(2, Box::new(Value::Bytes(vec![1]))),
            Value::from("b"),
        ),
    ]);
    assert!(value.canonicalize().is_err());
}

#[test]
fn bignums_are_reduced() {
    // Leading zeros are stripped and small bignums collapse to integers.
    let mut value = Value::Tag(2, Box::new(Value::Bytes(vec![0, 0, 42])));
    value.canonicalize().unwrap();
    assert_eq!(value, Value::from(42));

    let mut value = Value::Tag(3, Box::new(Value::Bytes(vec![9])));
    value.canonicalize().unwrap();
    assert_eq!(value, Value::from(-10));

    // An empty payload is zero.
    let mut value = Value::Tag(2, Box::new(Value::Bytes(vec![])));
    value.canonicalize().unwrap();
    assert_eq!(value, Value::from(0));

    // Nine or more significant bytes stay as a (minimal) bignum.
    let mut value = Value::Tag(
        2,
        Box::new(Value::Bytes(vec![0, 1, 0, 0, 0, 0, 0, 0, 0, 0])),
    );
    value.canonicalize().unwrap();
    assert_eq!(
        value,
        Value::Tag(2, Box::new(Value::Bytes(vec![1, 0, 0, 0, 0, 0, 0, 0, 0])))
    );

    // -2^64 is the most negative plain integer...
    let mut value = Value::Tag(3, Box::new(Value::Bytes(vec![255; 8])));
    value.canonicalize().unwrap();
    assert_eq!(
        cbor::to_vec(&value).unwrap(),
        hex::decode("3bffffffffffffffff").unwrap()
    );

    // ...and -2^64 - 1 stays a bignum.
    let mut value = Value::Tag(3, Box::new(Value::Bytes(vec![1, 0, 0, 0, 0, 0, 0, 0, 0])));
    value.canonicalize().unwrap();
    assert!(value.is_tag());
}

#[test]
fn nan_is_normalized() {
    let mut value = Value::Float(f64::from_bits(0x7ff8_dead_beef_0000));
    value.canonicalize().unwrap();
    assert_eq!(
        cbor::to_vec(&value).unwrap(),
        hex::decode("f97e00").unwrap()
    );
}

#[test]
fn to_canonical_vec_sorts_any_serialize() {
    // HashMap iteration order is nondeterministic; the canonical encoding
    // is not.
    let map: HashMap<&str, i32> = [("z", 1), ("aa", 2), ("b", 3), ("c", 4)].into();
    let bytes = cbor::to_canonical_vec(&map).unwrap();
    assert_eq!(
        hex::encode(&bytes),
        "a461620361630461 7a01626161 02".replace(' ', "")
    );

    // Struct fields are sorted too (here "b" < "a" is fixed up).
    #[derive(serde::Serialize)]
    struct Unsorted {
        b: u8,
        a: u8,
    }
    let bytes = cbor::to_canonical_vec(&Unsorted { b: 1, a: 2 }).unwrap();
    assert_eq!(hex::encode(&bytes), "a26161026162 01".replace(' ', ""));
}

#[test]
fn canonical_decode_encode_roundtrip_is_stable() {
    // Decoding an indefinite-length, unsorted document and re-encoding it
    // canonically yields a definite-length, sorted document; doing it
    // again is a fixed point.
    let messy = hex::decode("bf617a017f626161ff9f0102ffff").unwrap(); // {_ "z": 1, (_ "aa"): [_ 1, 2]}
    let value: Value = cbor::from_slice(&messy).unwrap();

    let once = cbor::to_canonical_vec(&value).unwrap();
    let twice = cbor::to_canonical_vec(&cbor::from_slice::<Value>(&once).unwrap()).unwrap();

    assert_eq!(once, twice);
    assert_eq!(hex::encode(&once), "a2617a01626161 820102".replace(' ', ""));
}
