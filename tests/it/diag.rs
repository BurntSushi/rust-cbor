//! Tests for diagnostic notation (RFC 8949 §8).

use cbor::{cbor, Value};

fn diag(hex: &str) -> String {
    let bytes = hex::decode(hex).unwrap();
    cbor::diagnostic(&bytes[..]).unwrap()
}

#[test]
fn appendix_a_diagnostic_column() {
    // The complete table from RFC 8949 Appendix A, verbatim.
    let table: &[(&str, &str)] = &[
        ("00", "0"),
        ("01", "1"),
        ("0a", "10"),
        ("17", "23"),
        ("1818", "24"),
        ("1819", "25"),
        ("1864", "100"),
        ("1903e8", "1000"),
        ("1a000f4240", "1000000"),
        ("1b000000e8d4a51000", "1000000000000"),
        ("1bffffffffffffffff", "18446744073709551615"),
        ("c249010000000000000000", "18446744073709551616"),
        ("3bffffffffffffffff", "-18446744073709551616"),
        ("c349010000000000000000", "-18446744073709551617"),
        ("20", "-1"),
        ("29", "-10"),
        ("3863", "-100"),
        ("3903e7", "-1000"),
        ("f90000", "0.0"),
        ("f98000", "-0.0"),
        ("f93c00", "1.0"),
        ("fb3ff199999999999a", "1.1"),
        ("f93e00", "1.5"),
        ("f97bff", "65504.0"),
        ("fa47c35000", "100000.0"),
        ("fa7f7fffff", "3.4028234663852886e+38"),
        ("fb7e37e43c8800759c", "1.0e+300"),
        ("f90001", "5.960464477539063e-8"),
        ("f90400", "0.00006103515625"),
        ("f9c400", "-4.0"),
        ("fbc010666666666666", "-4.1"),
        ("f97c00", "Infinity"),
        ("f97e00", "NaN"),
        ("f9fc00", "-Infinity"),
        ("fa7f800000", "Infinity"),
        ("fa7fc00000", "NaN"),
        ("faff800000", "-Infinity"),
        ("fb7ff0000000000000", "Infinity"),
        ("fb7ff8000000000000", "NaN"),
        ("fbfff0000000000000", "-Infinity"),
        ("f4", "false"),
        ("f5", "true"),
        ("f6", "null"),
        ("f7", "undefined"),
        ("f0", "simple(16)"),
        ("f8ff", "simple(255)"),
        (
            "c074323031332d30332d32315432303a30343a30305a",
            "0(\"2013-03-21T20:04:00Z\")",
        ),
        ("c11a514b67b0", "1(1363896240)"),
        ("c1fb41d452d9ec200000", "1(1363896240.5)"),
        ("d74401020304", "23(h'01020304')"),
        ("d818456449455446", "24(h'6449455446')"),
        (
            "d82076687474703a2f2f7777772e6578616d706c652e636f6d",
            "32(\"http://www.example.com\")",
        ),
        ("40", "h''"),
        ("4401020304", "h'01020304'"),
        ("60", "\"\""),
        ("6161", "\"a\""),
        ("6449455446", "\"IETF\""),
        ("62225c", "\"\\\"\\\\\""),
        ("62c3bc", "\"\\u00fc\""),
        ("63e6b0b4", "\"\\u6c34\""),
        ("64f0908591", "\"\\ud800\\udd51\""),
        ("80", "[]"),
        ("83010203", "[1, 2, 3]"),
        ("8301820203820405", "[1, [2, 3], [4, 5]]"),
        (
            "98190102030405060708090a0b0c0d0e0f101112131415161718181819",
            "[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]",
        ),
        ("a0", "{}"),
        ("a201020304", "{1: 2, 3: 4}"),
        ("a26161016162820203", "{\"a\": 1, \"b\": [2, 3]}"),
        ("826161a161626163", "[\"a\", {\"b\": \"c\"}]"),
        (
            "a56161614161626142616361436164614461656145",
            "{\"a\": \"A\", \"b\": \"B\", \"c\": \"C\", \"d\": \"D\", \"e\": \"E\"}",
        ),
        ("5f42010243030405ff", "(_ h'0102', h'030405')"),
        ("7f657374726561646d696e67ff", "(_ \"strea\", \"ming\")"),
        ("9fff", "[_ ]"),
        ("9f018202039f0405ffff", "[_ 1, [2, 3], [_ 4, 5]]"),
        ("9f01820203820405ff", "[_ 1, [2, 3], [4, 5]]"),
        ("83018202039f0405ff", "[1, [2, 3], [_ 4, 5]]"),
        ("83019f0203ff820405", "[1, [_ 2, 3], [4, 5]]"),
        (
            "9f0102030405060708090a0b0c0d0e0f101112131415161718181819ff",
            "[_ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]",
        ),
        ("bf61610161629f0203ffff", "{_ \"a\": 1, \"b\": [_ 2, 3]}"),
        ("826161bf61626163ff", "[\"a\", {_ \"b\": \"c\"}]"),
        ("bf6346756ef563416d7421ff", "{_ \"Fun\": true, \"Amt\": -2}"),
    ];

    for (hex, expected) in table {
        assert_eq!(diag(hex), *expected, "0x{hex}");
    }
}

#[test]
fn beyond_the_appendix() {
    // Empty indefinite forms.
    assert_eq!(diag("bfff"), "{_ }");
    assert_eq!(diag("5fff"), "(_ )");
    assert_eq!(diag("7fff"), "(_ )");

    // More simple values. (Two-byte encodings below 32 are not
    // well-formed, so simple(24)..=simple(31) cannot appear at all.)
    assert_eq!(diag("f820"), "simple(32)");

    // Bignum corner cases: empty payloads, leading zeros, payloads wider
    // than 128 bits, carry propagation in the negative form.
    assert_eq!(diag("c240"), "0");
    assert_eq!(diag("c340"), "-1");
    assert_eq!(diag("c24300002a"), "42");
    assert_eq!(diag("c341ff"), "-256");
    assert_eq!(
        diag(
            "c25101000000000000000000000000000000 00"
                .replace(' ', "")
                .as_str()
        ),
        "340282366920938463463374607431768211456" // 2^128
    );
    assert_eq!(
        diag(
            "c35101000000000000000000000000000000 00"
                .replace(' ', "")
                .as_str()
        ),
        "-340282366920938463463374607431768211457" // -(2^128) - 1
    );
    // A segmented bignum payload still reads as a number.
    assert_eq!(diag("c35f4101ff"), "-2");
    // A bignum tag with a non-bytes payload falls back to the tag form.
    assert_eq!(diag("c201"), "2(1)");
    assert_eq!(diag("c36161"), "3(\"a\")");

    // Nested tags.
    assert_eq!(diag("c1c24102"), "1(2)");
    assert_eq!(diag("d9d9f780"), "55799([])");

    // Control-character escapes.
    assert_eq!(
        diag("6a085c090a0c0d2f01207f"),
        "\"\\b\\\\\\t\\n\\f\\r/\\u0001 \\u007f\""
    );

    // Large bodies cross the internal 4096-byte chunking.
    let big = "a".repeat(5000);
    let bytes = cbor::to_vec(&big).unwrap();
    assert_eq!(cbor::diagnostic(&bytes[..]).unwrap(), format!("\"{big}\""));

    let blob = serde_bytes::ByteBuf::from(vec![0xabu8; 5000]);
    let bytes = cbor::to_vec(&blob).unwrap();
    assert_eq!(
        cbor::diagnostic(&bytes[..]).unwrap(),
        format!("h'{}'", "ab".repeat(5000))
    );

    // Multi-byte characters straddling the chunk boundary.
    let mut text = "a".repeat(4095);
    text.push_str("水水");
    let bytes = cbor::to_vec(&text).unwrap();
    assert_eq!(
        cbor::diagnostic(&bytes[..]).unwrap(),
        format!("\"{}\\u6c34\\u6c34\"", "a".repeat(4095))
    );
}

#[test]
fn malformed_input_is_rejected() {
    fn bad(hex: &str) {
        let bytes = hex::decode(hex).unwrap();
        assert!(cbor::diagnostic(&bytes[..]).is_err(), "0x{hex}");
    }

    bad(""); // empty
    bad("19"); // truncated argument
    bad("62"); // truncated text body
    bad("c2"); // truncated bignum
    bad("c241"); // truncated bignum payload
    bad("ff"); // lone break
    bad("81ff"); // break as a definite array element
    bad("bf6161ff"); // dangling key in an indefinite map
    bad("62fffe"); // invalid UTF-8
    bad("62c3"); // incomplete character at the end of the body
    bad("5f6161ff"); // text segment in a byte string
    bad("7f4161ff"); // byte segment in a text string
    bad("0001"); // trailing data
    bad("f801"); // reserved simple value encoding
    bad("41"); // truncated byte-string body
    bad("c2ff"); // break as a bignum payload

    // Errors strike inside every container position.
    bad("5f"); // indefinite bytes: missing segment header
    bad("5f41"); // indefinite bytes: truncated segment body
    bad("7f"); // indefinite text: missing segment header
    bad("7f61"); // indefinite text: truncated segment body
    bad("7f62fffeff"); // indefinite text: invalid segment
    bad("9f"); // indefinite array: missing element
    bad("9f62fffeff"); // indefinite array: invalid element
    bad("a162fffe01"); // definite map: invalid key
    bad("a10162fffe"); // definite map: invalid value
    bad("bf"); // indefinite map: missing key
    bad("bf62fffeff"); // indefinite map: invalid key
    bad("bf01"); // indefinite map: missing value
    bad("bf0162fffe"); // indefinite map: invalid value

    // Nesting is depth-limited for arrays, maps and tags alike.
    let mut bomb = vec![0xc1u8; 65536];
    *bomb.last_mut().unwrap() = 0x01;
    assert!(matches!(
        cbor::diagnostic(&bomb[..]),
        Err(cbor::de::Error::RecursionLimitExceeded)
    ));

    // I/O failures surface as such.
    struct FailReader;
    impl std::io::Read for FailReader {
        fn read(&mut self, _: &mut [u8]) -> std::io::Result<usize> {
            Err(std::io::Error::other("source broke"))
        }
    }
    assert!(matches!(
        cbor::diagnostic(FailReader),
        Err(cbor::de::Error::Io(..))
    ));
}

#[test]
fn value_display_is_diagnostic_notation() {
    assert_eq!(Value::from(1).to_string(), "1");
    assert_eq!(Value::from(-1).to_string(), "-1");
    assert_eq!(Value::from(u64::MAX).to_string(), "18446744073709551615");
    assert_eq!(Value::Bytes(vec![1, 2, 3]).to_string(), "h'010203'");
    assert_eq!(Value::Float(1.5).to_string(), "1.5");
    assert_eq!(Value::Float(f64::NAN).to_string(), "NaN");
    assert_eq!(Value::Float(f64::NEG_INFINITY).to_string(), "-Infinity");
    assert_eq!(Value::Float(-1.0e300).to_string(), "-1.0e+300");
    assert_eq!(Value::from("a\"水").to_string(), "\"a\\\"\\u6c34\"");
    assert_eq!(Value::Bool(false).to_string(), "false");
    assert_eq!(Value::Bool(true).to_string(), "true");
    assert_eq!(Value::Null.to_string(), "null");
    assert_eq!(
        Value::Tag(32, Box::new(Value::from("x"))).to_string(),
        "32(\"x\")"
    );
    assert_eq!(
        cbor!({ "k" => [1, -2.5, null], 2 => {} })
            .unwrap()
            .to_string(),
        r#"{"k": [1, -2.5, null], 2: {}}"#
    );

    // Bignum tags display as numbers, like in the appendix...
    assert_eq!(
        Value::from(u64::MAX as u128 + 1).to_string(),
        "18446744073709551616"
    );
    assert_eq!(
        Value::from(-(u64::MAX as i128) - 2).to_string(),
        "-18446744073709551617"
    );
    // ...unless the payload is not a byte string.
    assert_eq!(Value::Tag(2, Box::new(Value::Null)).to_string(), "2(null)");

    // Display through a failing formatter propagates the error.
    use std::fmt::Write as _;
    struct FailFmt;
    impl std::fmt::Write for FailFmt {
        fn write_str(&mut self, _: &str) -> std::fmt::Result {
            Err(std::fmt::Error)
        }
    }
    assert!(write!(FailFmt, "{}", Value::Null).is_err());

    // The wire form and the Value form agree wherever both can represent
    // the item.
    for value in [
        cbor!([1, "two", h_bytes(), 3.5]).unwrap(),
        cbor!({ "deep" => { 1 => [null, true] } }).unwrap(),
        Value::Tag(1, Box::new(Value::from(1363896240))),
    ] {
        let bytes = cbor::to_vec(&value).unwrap();
        assert_eq!(cbor::diagnostic(&bytes[..]).unwrap(), value.to_string());
    }

    fn h_bytes() -> Value {
        Value::Bytes(vec![0xde, 0xad])
    }
}

#[test]
fn float_formatting_boundaries() {
    // The plain/exponent switchover and digit-shifting paths.
    let cases: &[(f64, &str)] = &[
        (0.0, "0.0"),
        (-0.0, "-0.0"),
        (1e20, "100000000000000000000.0"),
        (1e21, "1.0e+21"),
        (1e-6, "0.000001"),
        (1e-7, "1.0e-7"),
        (1363896240.5, "1363896240.5"),
        (-65504.0, "-65504.0"),
        (5e-324, "5.0e-324"), // the smallest subnormal
        (f64::MAX, "1.7976931348623157e+308"),
    ];

    for (x, expected) in cases {
        assert_eq!(Value::Float(*x).to_string(), *expected, "{x:?}");
    }
}
