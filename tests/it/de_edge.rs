//! Edge-case and error-path tests for the streaming deserializer.

use std::collections::HashMap;

use cbor::de::Error;
use cbor::Value;
use serde::Deserialize;

fn de<T: serde::de::DeserializeOwned>(hex: &str) -> Result<T, Error> {
    cbor::from_slice(&hex::decode(hex).unwrap())
}

#[derive(Debug, PartialEq, Deserialize)]
enum Enum {
    Unit,
    Newtype(u32),
    Tuple(u32, u32),
    Struct { x: u32 },
}

#[test]
fn type_mismatches() {
    // Every typed entry point rejects a fundamentally wrong item.
    assert!(de::<bool>("01").is_err());
    assert!(de::<f64>("01").is_err());
    assert!(de::<u64>("6161").is_err()); // "a"
    assert!(de::<i64>("f4").is_err()); // false
    assert!(de::<char>("01").is_err());
    assert!(de::<String>("01").is_err());
    assert!(de::<serde_bytes::ByteBuf>("01").is_err());
    assert!(de::<Vec<u8>>("f4").is_err());
    assert!(de::<HashMap<String, u8>>("01").is_err());
    assert!(de::<()>("01").is_err());
    assert!(de::<Enum>("01").is_err());

    // The error messages name the unexpected item.
    let msg = de::<u64>("44deadbeef").unwrap_err().to_string();
    assert!(msg.contains("bytes"), "{msg}");
    let msg = de::<u64>("80").unwrap_err().to_string();
    assert!(msg.contains("sequence"), "{msg}");
    let msg = de::<u64>("a0").unwrap_err().to_string();
    assert!(msg.contains("map"), "{msg}");
    let msg = de::<u64>("f6").unwrap_err().to_string();
    assert!(msg.contains("null"), "{msg}");
    let msg = de::<u64>("f7").unwrap_err().to_string();
    assert!(msg.contains("undefined"), "{msg}");
    let msg = de::<u64>("f4").unwrap_err().to_string();
    assert!(msg.contains("false") || msg.contains("boolean"), "{msg}");
    let msg = de::<u64>("f93c00").unwrap_err().to_string();
    assert!(msg.contains('1'), "{msg}");
    let msg = de::<bool>("f0").unwrap_err().to_string();
    assert!(msg.contains("expected bool"), "{msg}");
}

#[test]
fn tags_are_skipped_in_typed_positions() {
    assert!(de::<bool>("c1f5").unwrap());
    assert_eq!(de::<f64>("c1f93c00").unwrap(), 1.0);
    assert_eq!(de::<f32>("c1f93c00").unwrap(), 1.0);
    assert_eq!(de::<char>("c16161").unwrap(), 'a');
    assert_eq!(de::<String>("c16161").unwrap(), "a");
    assert_eq!(de::<serde_bytes::ByteBuf>("c14101").unwrap().as_ref(), &[1]);
    assert_eq!(de::<Vec<u8>>("c18101").unwrap(), vec![1]);
    assert_eq!(
        de::<HashMap<String, u8>>("c1a1616101").unwrap(),
        [("a".to_string(), 1u8)].into()
    );
    de::<()>("c1f6").unwrap();
    assert_eq!(de::<Option<u64>>("c101").unwrap(), Some(1));
    assert_eq!(
        de::<Enum>("c1a1674e657774797065182a").unwrap(),
        Enum::Newtype(42)
    );
    // ...even several tags deep.
    assert_eq!(de::<u64>("c1c1c101").unwrap(), 1);
}

#[test]
fn chars() {
    assert_eq!(de::<char>("63e6b0b4").unwrap(), '水');
    // Two characters do not make a char, and neither do zero.
    assert!(de::<char>("626162").is_err());
    assert!(de::<char>("60").is_err());
    // Invalid UTF-8 inside a short text item is a syntax error.
    assert!(matches!(de::<char>("62fffe"), Err(Error::Syntax(0))));
    // A text item longer than four bytes cannot be a char.
    assert!(de::<char>("6568656c6c6f").is_err());
}

#[test]
fn bignum_errors() {
    // The bignum payload must be a byte string...
    assert!(de::<u64>("c201").is_err());
    // ...and small enough for the target type.
    assert!(de::<u64>("c249010101010101010101").is_err()); // 9 bytes
    assert!(de::<i64>("c349010101010101010101").is_err());
    let msg = de::<u128>(
        "c25101010101010101010101010101010101 01"
            .replace(' ', "")
            .as_str(),
    )
    .unwrap_err()
    .to_string();
    assert!(msg.contains("bigint too large"), "{msg}"); // 17 bytes
    assert!(de::<i128>(
        "c35101010101010101010101010101010101 01"
            .replace(' ', "")
            .as_str()
    )
    .is_err());
    // A negative bignum magnitude beyond i128.
    assert!(de::<i128>("c35080000000000000000000000000000000").is_err());
    // A positive bignum beyond i128, requested as signed.
    assert!(de::<i128>(
        "c25101010101010101010101010101010101 01"
            .replace(' ', "")
            .as_str()
    )
    .is_err());
    // Negative integers never fit unsigned types.
    let msg = de::<u64>("20").unwrap_err().to_string();
    assert!(msg.contains("unexpected negative"), "{msg}");
    assert!(de::<u128>("c34101").is_err());
}

#[test]
fn bignums_collapse_or_stay_tagged_in_any() {
    // In range: plain integers.
    assert_eq!(de::<Value>("c24101").unwrap(), Value::from(1));
    assert_eq!(de::<Value>("c34101").unwrap(), Value::from(-2));

    // A negative magnitude beyond i128 survives as a tagged byte string.
    let value = de::<Value>("c35080000000000000000000000000000000").unwrap();
    let (tag, inner) = value.as_tag().unwrap();
    assert_eq!(tag, 3);
    assert_eq!(inner.as_bytes().unwrap().len(), 16);

    // Leading zeros in bignums are tolerated everywhere.
    assert_eq!(de::<u8>("c243000007").unwrap(), 7);
    assert_eq!(de::<Value>("c243000007").unwrap(), Value::from(7));
}

#[test]
fn identifiers() {
    #[derive(Debug, PartialEq, Deserialize)]
    struct F {
        a: u8,
    }

    // Struct fields may arrive as byte strings...
    assert_eq!(de::<F>("a1416101").unwrap(), F { a: 1 });
    // ...or behind a tag.
    assert_eq!(de::<F>("a1c1616101").unwrap(), F { a: 1 });
    // Invalid UTF-8 in a field name is a syntax error.
    assert!(matches!(de::<F>("a162fffe01"), Err(Error::Syntax(1))));
    // Integer keys cannot name fields.
    let msg = de::<F>("a10102").unwrap_err().to_string();
    assert!(msg.contains("str or bytes"), "{msg}");
}

#[test]
fn enum_forms() {
    // The single-entry map form supports a unit variant with a null payload.
    assert_eq!(de::<Enum>("a164556e6974f6").unwrap(), Enum::Unit);
    // A unit variant with a non-null payload is rejected.
    assert!(de::<Enum>("a164556e697405").is_err());

    // The bare-text form only encodes unit variants.
    let text = |name: &str| cbor::to_vec(&name).unwrap();
    assert!(cbor::from_slice::<Enum>(&text("Newtype")).is_err());
    assert!(cbor::from_slice::<Enum>(&text("Tuple")).is_err());
    assert!(cbor::from_slice::<Enum>(&text("Struct")).is_err());

    // Indefinite-length maps do not encode enums.
    assert!(de::<Enum>("bf674e657774797065182aff").is_err());
    // Neither do multi-entry maps.
    assert!(de::<Enum>("a2674e657774797065182a6155f6").is_err());
}

#[test]
fn stream_iterator_errors() {
    // A syntax error at an item boundary surfaces as an error, not EOF.
    let mut iter = cbor::de::Deserializer::from_reader(&[0x01, 0x1c][..]).into_iter::<u32>();
    assert_eq!(iter.next().unwrap().unwrap(), 1);
    assert!(matches!(iter.next().unwrap(), Err(Error::Syntax(1))));
}

#[test]
fn indefinite_segment_majors_must_match() {
    // An indefinite byte string may not contain a text segment...
    assert!(matches!(de::<Value>("5f6161ff"), Err(Error::Syntax(1))));
    // ...and vice versa.
    assert!(matches!(de::<String>("7f4161ff"), Err(Error::Syntax(1))));
}

#[test]
fn deeply_tagged_input_hits_the_recursion_limit() {
    // Unknown tags recurse in deserialize_any; a tag bomb must error out.
    let bomb = vec![0xc1u8; 65536];
    assert!(matches!(
        cbor::from_slice::<Value>(&bomb),
        Err(Error::RecursionLimitExceeded)
    ));
}

#[test]
fn options_and_units() {
    assert_eq!(de::<Option<Option<u64>>>("f7").unwrap(), None);
    de::<()>("f7").unwrap();

    #[derive(Debug, PartialEq, Deserialize)]
    struct UnitStruct;
    de::<UnitStruct>("f6").unwrap();
    assert!(de::<UnitStruct>("01").is_err());
}

// Custom probes that call the borrowing entry points (`deserialize_str`,
// `deserialize_bytes`) directly; derived code only uses the owning forms.
#[derive(Debug, PartialEq)]
struct StrProbe(String);

impl<'de> Deserialize<'de> for StrProbe {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct V;

        impl serde::de::Visitor<'_> for V {
            type Value = String;

            fn expecting(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "a string")
            }

            fn visit_str<E: serde::de::Error>(self, v: &str) -> Result<String, E> {
                Ok(v.to_owned())
            }
        }

        deserializer.deserialize_str(V).map(StrProbe)
    }
}

#[derive(Debug, PartialEq)]
struct BytesProbe(Vec<u8>);

impl<'de> Deserialize<'de> for BytesProbe {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct V;

        impl serde::de::Visitor<'_> for V {
            type Value = Vec<u8>;

            fn expecting(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "bytes")
            }

            fn visit_bytes<E: serde::de::Error>(self, v: &[u8]) -> Result<Vec<u8>, E> {
                Ok(v.to_vec())
            }
        }

        deserializer.deserialize_bytes(V).map(BytesProbe)
    }
}

#[test]
fn borrowing_entry_points() {
    assert_eq!(de::<StrProbe>("6161").unwrap(), StrProbe("a".into()));
    assert_eq!(de::<BytesProbe>("4101").unwrap(), BytesProbe(vec![1]));
}

#[test]
fn more_unexpected_descriptions() {
    // A negative integer where a float was expected.
    let msg = de::<f64>("20").unwrap_err().to_string();
    assert!(msg.contains("-1"), "{msg}");

    // `true` where an integer was expected.
    let msg = de::<u64>("f5").unwrap_err().to_string();
    assert!(msg.contains("true") || msg.contains("boolean"), "{msg}");

    // A tag where the bignum payload was expected.
    let msg = de::<u64>("c2c101").unwrap_err().to_string();
    assert!(msg.contains("tag"), "{msg}");
}

#[test]
fn empty_input_fails_everywhere() {
    // Every entry point must propagate the missing-header error.
    assert!(de::<bool>("").is_err());
    assert!(de::<u64>("").is_err());
    assert!(de::<i64>("").is_err());
    assert!(de::<u128>("").is_err());
    assert!(de::<i128>("").is_err());
    assert!(de::<f32>("").is_err());
    assert!(de::<f64>("").is_err());
    assert!(de::<char>("").is_err());
    assert!(de::<String>("").is_err());
    assert!(de::<StrProbe>("").is_err());
    assert!(de::<serde_bytes::ByteBuf>("").is_err());
    assert!(de::<BytesProbe>("").is_err());
    assert!(de::<Vec<u8>>("").is_err());
    assert!(de::<(u8, u8)>("").is_err());
    assert!(de::<HashMap<String, u8>>("").is_err());
    assert!(de::<()>("").is_err());
    assert!(de::<Option<u8>>("").is_err());
    assert!(de::<Enum>("").is_err());
    assert!(de::<cbor::tag::AllowAny<u8>>("").is_err());
    assert!(de::<Value>("").is_err());
}

#[test]
fn truncated_arguments_and_bodies() {
    // Truncated multi-byte arguments.
    for hex in [
        "18",
        "19",
        "1a",
        "1b",
        "1901",
        "1a010203",
        "1b01020304050607",
    ] {
        assert!(matches!(de::<u64>(hex), Err(Error::Io(..))), "{hex}");
    }

    // A bignum tag with nothing behind it.
    assert!(de::<u64>("c2").is_err());
    assert!(de::<Value>("c2").is_err());

    // Truncated definite and segmented strings.
    assert!(de::<serde_bytes::ByteBuf>("42ff").is_err());
    assert!(de::<serde_bytes::ByteBuf>("5f").is_err());
    assert!(de::<serde_bytes::ByteBuf>("5f4101").is_err());
    assert!(de::<String>("7f").is_err());
    assert!(de::<String>("7f6161").is_err());

    // Truncated containers and enum payloads.
    assert!(de::<Vec<u8>>("8201").is_err());
    assert!(de::<HashMap<String, u8>>("a16161").is_err());
    assert!(de::<Enum>("a1").is_err());
    assert!(de::<Enum>("a1674e657774797065").is_err());
    assert!(de::<Option<u8>>("c1").is_err());
    assert!(de::<()>("c1").is_err());
    assert!(de::<Value>("9f01").is_err());
    assert!(de::<Value>("bf6161").is_err());
}

#[test]
fn nested_element_errors_propagate() {
    // Errors inside container elements surface through every access path.
    assert!(de::<Vec<u64>>("81f5").is_err()); // [true]
    assert!(de::<HashMap<String, u64>>("a16161f5").is_err()); // {"a": true}
    assert!(de::<HashMap<u64, u64>>("a1f501").is_err()); // {true: 1}
    assert!(de::<(u8, bool)>("820102").is_err()); // (1, 2)
    assert!(de::<Enum>("a1674e6577747970656161").is_err()); // {"Newtype": "a"}
    assert!(de::<Enum>("a1655475706c65820161").is_err()); // {"Tuple": [1, "a"]}
    assert!(de::<Enum>("a166537472756374a1617861").is_err()); // {"Struct": {"x": "a"}}
    assert!(de::<Option<u64>>("f5").is_err()); // Some(true)
    assert!(de::<cbor::tag::AllowAny<u64>>("c1f5").is_err()); // 1(true)
}

#[test]
fn truncated_bodies_in_every_position() {
    // A bignum payload header without its body.
    assert!(de::<u64>("c241").is_err());
    // A byte-string body cut short when read as a sequence.
    assert!(de::<Vec<u32>>("41").is_err());
    // Truncated field-name bodies, text and bytes.
    #[derive(Debug, Deserialize)]
    #[allow(dead_code)]
    struct F {
        a: u8,
    }
    assert!(de::<F>("a161").is_err());
    assert!(de::<F>("a141").is_err());
    // A truncated segment body inside an indefinite byte string.
    assert!(de::<serde_bytes::ByteBuf>("5f41").is_err());
    // An indefinite map with nothing after its header.
    assert!(de::<Value>("bf").is_err());
    assert!(de::<HashMap<String, u8>>("bf").is_err());
    // An indefinite array with nothing after its header.
    assert!(de::<Value>("9f").is_err());
}
