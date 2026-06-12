//! Tests for the allocation-free well-formedness validator.

use serde::Serialize;

fn ok(hex: &str) {
    let bytes = hex::decode(hex).unwrap();
    assert!(cbor::validate(&bytes[..]).is_ok(), "{hex} must validate");
}

fn bad(hex: &str) {
    let bytes = hex::decode(hex).unwrap();
    assert!(
        cbor::validate(&bytes[..]).is_err(),
        "{hex} must be rejected"
    );
}

#[test]
fn everything_we_encode_validates() {
    fn check<T: ?Sized + Serialize>(value: &T) {
        let bytes = cbor::to_vec(value).unwrap();
        assert!(cbor::validate(&bytes[..]).is_ok());
    }

    check(&true);
    check(&u64::MAX);
    check(&i64::MIN);
    check(&u128::MAX);
    check(&i128::MIN);
    check(&1.5f64);
    check(&f64::NAN);
    check(&'水');
    check(&"hello, world");
    check(&serde_bytes::ByteBuf::from(vec![0xab; 300]));
    check(&Option::<u8>::None);
    check(&(0..100).collect::<Vec<u64>>());
    check(&std::collections::BTreeMap::from([("k", 1u8), ("v", 2)]));
    check(&cbor::tag::AllowAny(Some(99), "tagged"));
    check(&cbor::cbor!({ "a" => [1, {"b" => null}], 2 => true }).unwrap());
}

#[test]
fn rfc_vectors_validate() {
    // A selection of RFC 8949 Appendix A vectors, including all the
    // indefinite-length forms.
    for hex in [
        "00",
        "1bffffffffffffffff",
        "3bffffffffffffffff",
        "c249010000000000000000",
        "f90000",
        "fb3ff199999999999a",
        "f97c00",
        "f4",
        "f6",
        "f7",
        "c074323031332d30332d32315432303a30343a30305a",
        "d74401020304",
        "64f0908591",
        "83018202039f0405ff",
        "9f018202039f0405ffff",
        "5f42010243030405ff",
        "7f657374726561646d696e67ff",
        "bf61610161629f0203ffff",
        "a26161016162820203",
        "80",
        "a0",
        "9fff",
        "bfff",
    ] {
        ok(hex);
    }

    // Unassigned simple values are well-formed, even though the serde
    // layer rejects them.
    ok("f0");
    ok("f8ff");
}

#[test]
fn malformed_input_is_rejected() {
    // Empty input and truncations everywhere.
    bad("");
    for hex in [
        "18", "19", "1a", "1b", "61", "41", "5f", "5f41", "7f", "7f6161", "9f", "bf", "bf01", "a1",
        "a16161", "81", "c2", "8201", "9f01", "62c3",
    ] {
        bad(hex);
    }

    // Reserved additional information and malformed simple values.
    for hex in ["1c", "1d", "1e", "fc", "f800", "f81f", "1f", "3f", "df"] {
        bad(hex);
    }

    // Misplaced breaks.
    bad("ff"); // lone break
    bad("81ff"); // break as a definite array element
    bad("a1ff"); // break as a definite map key
    bad("bf6161ff"); // break in place of a map value (dangling key)
    bad("bf62fffeff"); // invalid element inside an indefinite map
    bad("c2ff"); // break as a tag payload

    // Indefinite string segments of the wrong shape.
    bad("5f6161ff"); // text segment in a byte string
    bad("7f4161ff"); // byte segment in a text string
    bad("5f5f4101ffff"); // nested indefinite segments
    bad("5f00ff"); // integer segment

    // Invalid UTF-8, in one piece and per segment.
    bad("62fffe");
    bad("7f62fffeff");
    bad("7f61e261829461acff"); // characters split across segments

    // Trailing data.
    bad("0001");
    bad("f6f6");

    // Forged lengths fail without allocating.
    bad("5bffffffffffffffff");
    bad("7bffffffffffffffff");
    bad("9bffffffffffffffff");
    bad("bbffffffffffffffff");
}

#[test]
fn nesting_is_depth_limited() {
    let mut array_bomb = vec![0x81u8; 65536];
    *array_bomb.last_mut().unwrap() = 0x01;
    assert!(matches!(
        cbor::validate(&array_bomb[..]),
        Err(cbor::de::Error::RecursionLimitExceeded)
    ));

    let mut tag_bomb = vec![0xc1u8; 65536];
    *tag_bomb.last_mut().unwrap() = 0x01;
    assert!(matches!(
        cbor::validate(&tag_bomb[..]),
        Err(cbor::de::Error::RecursionLimitExceeded)
    ));

    // Mixed indefinite nesting is limited too.
    let mut mixed = vec![0x9fu8; 65536];
    *mixed.last_mut().unwrap() = 0x01;
    assert!(matches!(
        cbor::validate(&mixed[..]),
        Err(cbor::de::Error::RecursionLimitExceeded)
    ));
}

#[test]
fn utf8_across_chunk_boundaries() {
    // The validator checks text bodies in 4096-byte chunks; place
    // multi-byte characters across the boundary.
    for prefix_len in [4094usize, 4095, 4096] {
        let mut text = "a".repeat(prefix_len);
        text.push_str("水水");
        let bytes = cbor::to_vec(&text).unwrap();
        assert!(cbor::validate(&bytes[..]).is_ok(), "prefix {prefix_len}");
    }

    // An invalid byte after the chunk boundary is still caught...
    let mut body = vec![0x61u8; 5000];
    body[4500] = 0xff;
    let mut bytes = vec![0x7a, 0x00, 0x00, 0x13, 0x88]; // text(5000)
    bytes.extend_from_slice(&body);
    assert!(cbor::validate(&bytes[..]).is_err());

    // ...and so is an incomplete character at the very end of the body.
    let mut bytes = vec![0x7a, 0x00, 0x00, 0x13, 0x88];
    let mut body = vec![0x61u8; 4999];
    body.push(0xc3); // first byte of a two-byte character
    bytes.extend_from_slice(&body);
    assert!(cbor::validate(&bytes[..]).is_err());
}

#[test]
fn io_errors_propagate() {
    use std::io::Read;

    struct FailReader;

    impl Read for FailReader {
        fn read(&mut self, _: &mut [u8]) -> std::io::Result<usize> {
            Err(std::io::Error::other("source broke"))
        }
    }

    // A failure while reading the item is an I/O error...
    assert!(matches!(
        cbor::validate(FailReader),
        Err(cbor::de::Error::Io(..))
    ));

    // ...and so is a failure while probing for trailing data.
    let reader = (&[0x01u8][..]).chain(FailReader);
    assert!(matches!(
        cbor::validate(reader),
        Err(cbor::de::Error::Io(..))
    ));
}
