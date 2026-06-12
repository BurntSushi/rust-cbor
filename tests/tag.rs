//! Tests for CBOR tag support.

use cbor::tag::{AllowAny, AllowExact, RequireAny, RequireExact};
use cbor::Value;

#[test]
fn require_exact() {
    // Tag 0: standard date/time string.
    let datetime = RequireExact::<String, 0>("2013-03-21T20:04:00Z".into());
    let bytes = cbor::to_vec(&datetime).unwrap();
    assert_eq!(
        hex::encode(&bytes),
        "c074323031332d30332d32315432303a30343a30305a"
    );

    let back: RequireExact<String, 0> = cbor::from_slice(&bytes).unwrap();
    assert_eq!(back, datetime);

    // The wrong tag is rejected...
    assert!(cbor::from_slice::<RequireExact<String, 1>>(&bytes).is_err());
    // ...and so is a missing tag.
    let untagged = cbor::to_vec(&"2013-03-21T20:04:00Z").unwrap();
    assert!(cbor::from_slice::<RequireExact<String, 0>>(&untagged).is_err());
}

#[test]
fn allow_exact() {
    let bytes = cbor::to_vec(&AllowExact::<u64, 1>(1363896240)).unwrap();
    assert_eq!(hex::encode(&bytes), "c11a514b67b0");

    // Tagged and untagged input both decode.
    let tagged: AllowExact<u64, 1> = cbor::from_slice(&bytes).unwrap();
    assert_eq!(tagged.0, 1363896240);

    let untagged_bytes = cbor::to_vec(&1363896240u64).unwrap();
    let untagged: AllowExact<u64, 1> = cbor::from_slice(&untagged_bytes).unwrap();
    assert_eq!(untagged.0, 1363896240);

    // A different tag is rejected.
    assert!(cbor::from_slice::<AllowExact<u64, 7>>(&bytes).is_err());
}

#[test]
fn require_any() {
    let bytes = cbor::to_vec(&RequireAny(32, String::from("https://example.com"))).unwrap();
    let back: RequireAny<String> = cbor::from_slice(&bytes).unwrap();
    assert_eq!(back.0, 32);
    assert_eq!(back.1, "https://example.com");

    let untagged = cbor::to_vec(&"https://example.com").unwrap();
    assert!(cbor::from_slice::<RequireAny<String>>(&untagged).is_err());
}

#[test]
fn allow_any() {
    let tagged = hex::decode("c11a514b67b0").unwrap();
    let back: AllowAny<u64> = cbor::from_slice(&tagged).unwrap();
    assert_eq!(back, AllowAny(Some(1), 1363896240));

    let untagged = cbor::to_vec(&1363896240u64).unwrap();
    let back: AllowAny<u64> = cbor::from_slice(&untagged).unwrap();
    assert_eq!(back, AllowAny(None, 1363896240));

    // Round trip preserves the tag (or its absence).
    let bytes = cbor::to_vec(&AllowAny(Some(1), 1363896240u64)).unwrap();
    assert_eq!(hex::encode(&bytes), "c11a514b67b0");
    let bytes = cbor::to_vec(&AllowAny(None, 1363896240u64)).unwrap();
    assert_eq!(hex::encode(&bytes), "1a514b67b0");
}

#[test]
fn value_tags() {
    // Tags survive a round trip through Value.
    let value = Value::Tag(262, Box::new(Value::from("x")));
    let bytes = cbor::to_vec(&value).unwrap();
    assert_eq!(hex::encode(&bytes), "d901066178");
    let back: Value = cbor::from_slice(&bytes).unwrap();
    assert_eq!(back, value);

    // Nested tags survive too. (Note that a nested *bignum* tag would
    // collapse into an integer by design.)
    let nested = Value::Tag(1, Box::new(Value::Tag(0, Box::new(Value::from("x")))));
    let back: Value = cbor::from_slice(&cbor::to_vec(&nested).unwrap()).unwrap();
    assert_eq!(back, nested);

    // Value and the tag wrappers interconvert.
    let wrapped: RequireAny<String> = value.deserialized().unwrap();
    assert_eq!(wrapped, RequireAny(262, "x".into()));
    let again = Value::serialized(&wrapped).unwrap();
    assert_eq!(again, value);
}

#[test]
fn oversized_bignums_stay_tagged() {
    // A bignum wider than 128 bits cannot collapse into an integer, so it
    // survives as a tagged byte string.
    let mut payload = vec![1u8];
    payload.extend_from_slice(&[0u8; 16]);

    let value = Value::Tag(2, Box::new(Value::Bytes(payload)));
    let bytes = cbor::to_vec(&value).unwrap();
    let back: Value = cbor::from_slice(&bytes).unwrap();
    assert_eq!(back, value);

    // While a small one collapses.
    let small = Value::Tag(2, Box::new(Value::Bytes(vec![42])));
    let bytes = cbor::to_vec(&small).unwrap();
    let back: Value = cbor::from_slice(&bytes).unwrap();
    assert_eq!(back, Value::from(42));
}
