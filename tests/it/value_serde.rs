//! Exhaustive tests for `Value::serialized` and `Value::deserialized`.

use std::collections::{BTreeMap, HashMap};

use cbor::{cbor, Value};
use serde::{Deserialize, Serialize};

#[derive(Debug, PartialEq, Deserialize, Serialize)]
enum Enum {
    Unit,
    Newtype(u32),
    Tuple(u32, u32),
    Struct { x: u32 },
}

#[derive(Debug, PartialEq, Deserialize, Serialize)]
struct Plain {
    a: u8,
    b: String,
}

#[derive(Debug, PartialEq, Deserialize, Serialize)]
struct NewtypeStruct(u8);

#[derive(Debug, PartialEq, Deserialize, Serialize)]
struct TupleStruct(u8, bool);

#[derive(Debug, PartialEq, Deserialize, Serialize)]
struct UnitStruct;

#[test]
fn serialized_shapes() {
    assert_eq!(Value::serialized(&true).unwrap(), Value::Bool(true));
    assert_eq!(Value::serialized(&7u8).unwrap(), Value::from(7));
    assert_eq!(Value::serialized(&7u16).unwrap(), Value::from(7));
    assert_eq!(Value::serialized(&7u32).unwrap(), Value::from(7));
    assert_eq!(Value::serialized(&7u64).unwrap(), Value::from(7));
    assert_eq!(Value::serialized(&-7i8).unwrap(), Value::from(-7));
    assert_eq!(Value::serialized(&-7i16).unwrap(), Value::from(-7));
    assert_eq!(Value::serialized(&-7i32).unwrap(), Value::from(-7));
    assert_eq!(Value::serialized(&-7i64).unwrap(), Value::from(-7));
    assert_eq!(
        Value::serialized(&u128::MAX).unwrap(),
        Value::from(u128::MAX)
    );
    assert_eq!(
        Value::serialized(&i128::MIN).unwrap(),
        Value::from(i128::MIN)
    );
    assert_eq!(Value::serialized(&1.5f32).unwrap(), Value::Float(1.5));
    assert_eq!(Value::serialized(&1.5f64).unwrap(), Value::Float(1.5));
    assert_eq!(Value::serialized(&'水').unwrap(), Value::from('水'));
    assert_eq!(Value::serialized("hi").unwrap(), Value::from("hi"));
    assert_eq!(
        Value::serialized(&serde_bytes::ByteBuf::from(vec![1u8])).unwrap(),
        Value::Bytes(vec![1])
    );

    assert_eq!(Value::serialized(&Option::<u8>::None).unwrap(), Value::Null);
    assert_eq!(Value::serialized(&Some(1u8)).unwrap(), Value::from(1));
    assert_eq!(Value::serialized(&()).unwrap(), Value::Null);
    assert_eq!(Value::serialized(&UnitStruct).unwrap(), Value::Null);
    assert_eq!(
        Value::serialized(&NewtypeStruct(9)).unwrap(),
        Value::from(9)
    );

    assert_eq!(
        Value::serialized(&vec![1u8, 2]).unwrap(),
        cbor!([1, 2]).unwrap()
    );
    assert_eq!(
        Value::serialized(&(1u8, true)).unwrap(),
        Value::Array(vec![Value::from(1), Value::Bool(true)])
    );
    assert_eq!(
        Value::serialized(&TupleStruct(1, true)).unwrap(),
        Value::Array(vec![Value::from(1), Value::Bool(true)])
    );

    let map: BTreeMap<&str, u8> = [("k", 1)].into();
    assert_eq!(Value::serialized(&map).unwrap(), cbor!({"k" => 1}).unwrap());

    assert_eq!(
        Value::serialized(&Plain {
            a: 1,
            b: "x".into()
        })
        .unwrap(),
        cbor!({"a" => 1, "b" => "x"}).unwrap()
    );

    assert_eq!(Value::serialized(&Enum::Unit).unwrap(), Value::from("Unit"));
    assert_eq!(
        Value::serialized(&Enum::Newtype(7)).unwrap(),
        cbor!({"Newtype" => 7}).unwrap()
    );
    assert_eq!(
        Value::serialized(&Enum::Tuple(1, 2)).unwrap(),
        cbor!({"Tuple" => [1, 2]}).unwrap()
    );
    assert_eq!(
        Value::serialized(&Enum::Struct { x: 7 }).unwrap(),
        cbor!({"Struct" => {"x" => 7}}).unwrap()
    );

    // Value-to-Value is the identity.
    let value = cbor!({ "t" => [1, null] }).unwrap();
    assert_eq!(Value::serialized(&value).unwrap(), value);
    let tagged = Value::Tag(7, Box::new(Value::from(1)));
    assert_eq!(Value::serialized(&tagged).unwrap(), tagged);
}

// Emits the internal tag protocol with a non-integer tag field.
struct BadTagNumber;

impl Serialize for BadTagNumber {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeTupleVariant;
        let mut acc = serializer.serialize_tuple_variant("@@TAG@@", 1, "@@TAGGED@@", 2)?;
        acc.serialize_field("not a number")?;
        acc.serialize_field(&0u8)?;
        acc.end()
    }
}

// Emits the internal tag protocol but stops after the tag number.
struct HalfATag;

impl Serialize for HalfATag {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeTupleVariant;
        let mut acc = serializer.serialize_tuple_variant("@@TAG@@", 1, "@@TAGGED@@", 2)?;
        acc.serialize_field(&1u64)?;
        acc.end()
    }
}

#[test]
fn malformed_tag_protocol_is_rejected() {
    let err = Value::serialized(&BadTagNumber).unwrap_err();
    assert!(err.to_string().contains("expected tag"));

    let err = cbor::to_vec(&BadTagNumber).unwrap_err();
    assert!(err.to_string().contains("expected tag"));

    let err = Value::serialized(&HalfATag).unwrap_err();
    assert!(err.to_string().contains("invalid tag input"));
}

// Both of this crate's serializers and deserializers are binary formats.
struct HumanCheck;

impl Serialize for HumanCheck {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        assert!(!serializer.is_human_readable());
        serializer.serialize_unit()
    }
}

impl<'de> Deserialize<'de> for HumanCheck {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        assert!(!deserializer.is_human_readable());
        <()>::deserialize(deserializer)?;
        Ok(HumanCheck)
    }
}

#[test]
fn binary_format() {
    assert_eq!(Value::serialized(&HumanCheck).unwrap(), Value::Null);
    let bytes = cbor::to_vec(&HumanCheck).unwrap();
    let _: HumanCheck = cbor::from_slice(&bytes).unwrap();
    let _: HumanCheck = Value::Null.deserialized().unwrap();
}

#[test]
fn deserialized_scalars() {
    assert!(Value::Bool(true).deserialized::<bool>().unwrap());
    assert!(Value::from(1).deserialized::<bool>().is_err());

    let int = Value::from(7);
    assert_eq!(int.deserialized::<u8>().unwrap(), 7);
    assert_eq!(int.deserialized::<u16>().unwrap(), 7);
    assert_eq!(int.deserialized::<u32>().unwrap(), 7);
    assert_eq!(int.deserialized::<u64>().unwrap(), 7);
    assert_eq!(int.deserialized::<u128>().unwrap(), 7);
    let neg = Value::from(-7);
    assert_eq!(neg.deserialized::<i8>().unwrap(), -7);
    assert_eq!(neg.deserialized::<i16>().unwrap(), -7);
    assert_eq!(neg.deserialized::<i32>().unwrap(), -7);
    assert_eq!(neg.deserialized::<i64>().unwrap(), -7);
    assert_eq!(neg.deserialized::<i128>().unwrap(), -7);
    assert!(neg.deserialized::<u8>().is_err());
    assert!(Value::from(300).deserialized::<u8>().is_err());
    assert!(Value::Null.deserialized::<u8>().is_err());

    assert_eq!(Value::Float(1.5).deserialized::<f32>().unwrap(), 1.5);
    assert_eq!(Value::Float(1.5).deserialized::<f64>().unwrap(), 1.5);
    assert!(Value::from(1).deserialized::<f64>().is_err());

    assert_eq!(Value::from("x").deserialized::<char>().unwrap(), 'x');
    assert!(Value::from("xy").deserialized::<char>().is_err());
    assert!(Value::from("").deserialized::<char>().is_err());
    assert!(Value::from(1).deserialized::<char>().is_err());

    assert_eq!(Value::from("hi").deserialized::<String>().unwrap(), "hi");
    assert!(Value::from(1).deserialized::<String>().is_err());

    let bytes = Value::Bytes(vec![1, 2]);
    assert_eq!(
        bytes
            .deserialized::<serde_bytes::ByteBuf>()
            .unwrap()
            .as_ref(),
        &[1, 2]
    );
    // An array of integers deserializes as bytes too.
    let array = cbor!([1, 2]).unwrap();
    assert_eq!(
        array
            .deserialized::<serde_bytes::ByteBuf>()
            .unwrap()
            .as_ref(),
        &[1, 2]
    );
    assert!(Value::from(1)
        .deserialized::<serde_bytes::ByteBuf>()
        .is_err());
}

#[test]
fn deserialized_bignums() {
    let big = |bytes: &[u8]| Value::Tag(2, Box::new(Value::Bytes(bytes.to_vec())));
    let bigneg = |bytes: &[u8]| Value::Tag(3, Box::new(Value::Bytes(bytes.to_vec())));

    // Small bignums collapse into any integer type, leading zeros and all.
    assert_eq!(big(&[0, 0, 7]).deserialized::<u8>().unwrap(), 7);
    assert_eq!(bigneg(&[7]).deserialized::<i8>().unwrap(), -8);
    assert_eq!(
        big(&[1; 16]).deserialized::<u128>().unwrap(),
        u128::from_be_bytes([1; 16])
    );

    // Oversized payloads do not fit.
    assert!(big(&[1; 17]).deserialized::<u128>().is_err());
    assert!(bigneg(&[1; 17]).deserialized::<i128>().is_err());
    assert!(big(&[1; 16]).deserialized::<u8>().is_err());
    // A negative magnitude beyond i128 does not fit either.
    assert!(bigneg(&[0x80; 16]).deserialized::<i128>().is_err());
    // A negative value never fits an unsigned (or too-narrow) type.
    assert!(bigneg(&[7]).deserialized::<u8>().is_err());
    assert!(bigneg(&[1, 0]).deserialized::<i8>().is_err());

    // The payload must be a byte string.
    let weird = Value::Tag(2, Box::new(Value::from("x")));
    assert!(weird.deserialized::<u64>().is_err());

    // Tags other than bignums are not integers.
    let other = Value::Tag(7, Box::new(Value::from("x")));
    assert!(other.deserialized::<u64>().is_err());
}

#[test]
fn deserialized_collections() {
    let array = cbor!([1, 2, 3]).unwrap();
    assert_eq!(array.deserialized::<Vec<u8>>().unwrap(), vec![1, 2, 3]);
    assert_eq!(array.deserialized::<(u8, u8, u8)>().unwrap(), (1, 2, 3));
    assert!(Value::from(1).deserialized::<Vec<u8>>().is_err());

    let pair = cbor!([1, true]).unwrap();
    assert_eq!(
        pair.deserialized::<TupleStruct>().unwrap(),
        TupleStruct(1, true)
    );

    let map = cbor!({"a" => 1, "b" => "x"}).unwrap();
    assert_eq!(
        map.deserialized::<Plain>().unwrap(),
        Plain {
            a: 1,
            b: "x".into()
        }
    );
    let simple = cbor!({"k" => 1}).unwrap();
    assert_eq!(
        simple.deserialized::<BTreeMap<String, u8>>().unwrap(),
        [("k".to_string(), 1u8)].into()
    );
    assert_eq!(
        simple.deserialized::<HashMap<String, u8>>().unwrap(),
        [("k".to_string(), 1u8)].into()
    );
    assert!(Value::from(1)
        .deserialized::<BTreeMap<String, u8>>()
        .is_err());

    // Unknown fields are ignored (of any shape).
    let extra = cbor!({
        "a" => 1,
        "b" => "x",
        "ignored" => { "deep" => [1, 2, {"k" => null}] },
    })
    .unwrap();
    assert_eq!(
        extra.deserialized::<Plain>().unwrap(),
        Plain {
            a: 1,
            b: "x".into()
        }
    );
}

#[test]
fn deserialized_options_and_units() {
    assert_eq!(Value::Null.deserialized::<Option<u8>>().unwrap(), None);
    assert_eq!(
        Value::from(1).deserialized::<Option<u8>>().unwrap(),
        Some(1)
    );
    Value::Null.deserialized::<()>().unwrap();
    assert!(Value::from(1).deserialized::<()>().is_err());
    Value::Null.deserialized::<UnitStruct>().unwrap();
    assert_eq!(
        Value::from(9).deserialized::<NewtypeStruct>().unwrap(),
        NewtypeStruct(9)
    );
}

#[test]
fn deserialized_enums() {
    // The bare-text form encodes a unit variant.
    assert_eq!(
        Value::from("Unit").deserialized::<Enum>().unwrap(),
        Enum::Unit
    );

    // The single-entry-map form encodes the rest.
    let newtype = cbor!({"Newtype" => 7}).unwrap();
    assert_eq!(newtype.deserialized::<Enum>().unwrap(), Enum::Newtype(7));
    let tuple = cbor!({"Tuple" => [1, 2]}).unwrap();
    assert_eq!(tuple.deserialized::<Enum>().unwrap(), Enum::Tuple(1, 2));
    let strukt = cbor!({"Struct" => {"x" => 7}}).unwrap();
    assert_eq!(
        strukt.deserialized::<Enum>().unwrap(),
        Enum::Struct { x: 7 }
    );
    let unit = cbor!({"Unit" => null}).unwrap();
    assert_eq!(unit.deserialized::<Enum>().unwrap(), Enum::Unit);

    // Tags in front of the enum are transparent.
    let tagged = Value::Tag(99, Box::new(newtype));
    assert_eq!(tagged.deserialized::<Enum>().unwrap(), Enum::Newtype(7));

    // Shape mismatches are rejected.
    assert!(Value::from(1).deserialized::<Enum>().is_err());
    let unit_with_payload = cbor!({"Unit" => 5}).unwrap();
    assert!(unit_with_payload.deserialized::<Enum>().is_err());
    let not_an_array = cbor!({"Tuple" => 5}).unwrap();
    assert!(not_an_array.deserialized::<Enum>().is_err());
    let not_a_map = cbor!({"Struct" => 5}).unwrap();
    assert!(not_a_map.deserialized::<Enum>().is_err());
    let two_entries = cbor!({"Newtype" => 7, "Tuple" => [1, 2]}).unwrap();
    assert!(two_entries.deserialized::<Enum>().is_err());
}

#[test]
fn deserialized_unwraps_tags_for_scalars() {
    let tag = |v: Value| Value::Tag(7, Box::new(v));

    assert!(tag(Value::Bool(true)).deserialized::<bool>().unwrap());
    assert_eq!(tag(Value::Float(1.5)).deserialized::<f64>().unwrap(), 1.5);
    assert_eq!(tag(Value::from("x")).deserialized::<char>().unwrap(), 'x');
    assert_eq!(
        tag(Value::from("hi")).deserialized::<String>().unwrap(),
        "hi"
    );
    assert_eq!(
        tag(Value::Bytes(vec![1]))
            .deserialized::<serde_bytes::ByteBuf>()
            .unwrap()
            .as_ref(),
        &[1]
    );
    assert_eq!(
        tag(cbor!([1]).unwrap()).deserialized::<Vec<u8>>().unwrap(),
        vec![1]
    );
    assert_eq!(
        tag(cbor!({"k" => 1}).unwrap())
            .deserialized::<BTreeMap<String, u8>>()
            .unwrap(),
        [("k".to_string(), 1u8)].into()
    );
}

#[test]
fn deserialized_error_messages_name_the_input() {
    // The invalid_type errors carry a description of the unexpected value.
    let err = |v: &Value| v.deserialized::<bool>().unwrap_err().to_string();

    assert!(err(&Value::from(7)).contains('7'));
    assert!(err(&Value::from(-7)).contains("-7"));
    assert!(err(&Value::from(u64::MAX)).contains("18446744073709551615"));
    assert!(err(&Value::from(-(u64::MAX as i128) - 1)).contains("large integer"));
    assert!(err(&Value::Float(0.5)).contains("0.5"));
    assert!(err(&Value::from("s")).contains('s'));
    assert!(err(&Value::Bytes(vec![1])).contains("bool"));
    assert!(err(&Value::Array(vec![])).contains("sequence"));
    assert!(err(&Value::Map(vec![])).contains("map"));
    assert!(Value::Null
        .deserialized::<u8>()
        .unwrap_err()
        .to_string()
        .contains("null"));
    let tagged = Value::Tag(9, Box::new(Value::Null));
    assert!(tagged
        .deserialized::<u8>()
        .unwrap_err()
        .to_string()
        .contains("tag"));
    assert!(Value::Bool(true)
        .deserialized::<String>()
        .unwrap_err()
        .to_string()
        .contains("bool"));
}

#[test]
fn roundtrip_through_value_equals_direct_wire() {
    // serialized() then to_vec() must equal to_vec() directly, and the
    // decoded Value must deserialize back to the original.
    macro_rules! check {
        ($t:ty, $v:expr) => {{
            let v: $t = $v;
            let direct = cbor::to_vec(&v).unwrap();
            let through = cbor::to_vec(&Value::serialized(&v).unwrap()).unwrap();
            assert_eq!(direct, through);
            let value: Value = cbor::from_slice(&direct).unwrap();
            assert_eq!(value.deserialized::<$t>().unwrap(), v);
        }};
    }

    check!(bool, true);
    check!(i32, -300);
    check!(u64, u64::MAX);
    check!(u128, u128::MAX);
    check!(i128, i128::MIN);
    check!(f64, 1.5);
    check!(String, "水".into());
    check!(Vec<u8>, vec![1, 2, 3]);
    check!(
        Plain,
        Plain {
            a: 1,
            b: "x".into()
        }
    );
    check!(Enum, Enum::Unit);
    check!(Enum, Enum::Struct { x: 7 });
    check!(Option<u8>, None);
}

#[test]
fn value_identity_through_deserialized() {
    // Each Value variant survives Value -> Value deserialization.
    let samples = [
        Value::Bool(true),
        Value::from(7),
        Value::from(-7),
        Value::from(u64::MAX),
        Value::from(-2i128.pow(64)), // i128 path of deserialize_any
        Value::Float(1.5),
        Value::from("hi"),
        Value::Bytes(vec![1, 2]),
        Value::Null,
        Value::Tag(9, Box::new(Value::from(1))),
        Value::Array(vec![Value::Null]),
        Value::Map(vec![(Value::from(1), Value::Null)]),
    ];

    for value in samples {
        assert_eq!(value.deserialized::<Value>().unwrap(), value, "{value:?}");
    }
}

#[test]
fn tag_wrappers_from_values() {
    use cbor::tag::AllowAny;

    // An untagged value satisfies AllowAny without a tag.
    let plain = Value::from(5);
    assert_eq!(
        plain.deserialized::<AllowAny<u64>>().unwrap(),
        AllowAny(None, 5)
    );

    let tagged = Value::Tag(1, Box::new(Value::from(5)));
    assert_eq!(
        tagged.deserialized::<AllowAny<u64>>().unwrap(),
        AllowAny(Some(1), 5)
    );
}

#[test]
fn oversized_bignum_payloads_skip_leading_zeros() {
    // More than 16 bytes, but only because of leading zeros: still fits.
    let mut payload = vec![0u8, 0];
    payload.extend_from_slice(&[1; 16]);
    let value = Value::Tag(2, Box::new(Value::Bytes(payload)));
    assert_eq!(
        value.deserialized::<u128>().unwrap(),
        u128::from_be_bytes([1; 16])
    );
}

// Emits the tag protocol with a first field that cannot be a tag number
// because it is itself a tagged value.
struct TagInTagNumber;

impl Serialize for TagInTagNumber {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeTupleVariant;
        let mut acc = serializer.serialize_tuple_variant("@@TAG@@", 1, "@@TAGGED@@", 2)?;
        acc.serialize_field(&Value::Tag(1, Box::new(Value::Null)))?;
        acc.serialize_field(&0u8)?;
        acc.end()
    }
}

#[test]
fn tag_protocol_rejects_tagged_tag_numbers() {
    assert!(Value::serialized(&TagInTagNumber).is_err());
    assert!(cbor::to_vec(&TagInTagNumber).is_err());
}

// A deserializer that presents data through the visitor methods the CBOR
// deserializers never use, validating the Value visitor's remaining arms.
mod foreign {
    use serde::de::value::{Error as DeError, U64Deserializer};
    use serde::de::{self, IntoDeserializer};
    use serde::forward_to_deserialize_any;
    use serde::Deserialize;

    use cbor::Value;

    pub enum Mode {
        Some,
        Unit,
        NewtypeStruct,
        Nothing,
    }

    pub struct WeirdDe(pub Mode);

    impl<'de> de::Deserializer<'de> for WeirdDe {
        type Error = DeError;

        fn deserialize_any<V: de::Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
            match self.0 {
                Mode::Some => visitor.visit_some(5u64.into_deserializer()),
                Mode::Unit => visitor.visit_unit(),
                Mode::NewtypeStruct => {
                    visitor.visit_newtype_struct(U64Deserializer::<DeError>::new(5))
                }
                Mode::Nothing => Err(de::Error::invalid_type(
                    de::Unexpected::Other("nothing"),
                    &visitor,
                )),
            }
        }

        forward_to_deserialize_any! {
            i8 i16 i32 i64 i128 u8 u16 u32 u64 u128
            bool f32 f64 char str string bytes byte_buf
            seq map struct tuple tuple_struct identifier ignored_any
            option unit unit_struct newtype_struct enum
        }
    }

    #[test]
    fn value_absorbs_unusual_visits() {
        assert_eq!(
            Value::deserialize(WeirdDe(Mode::Some)).unwrap(),
            Value::from(5)
        );
        assert_eq!(
            Value::deserialize(WeirdDe(Mode::Unit)).unwrap(),
            Value::Null
        );
        assert_eq!(
            Value::deserialize(WeirdDe(Mode::NewtypeStruct)).unwrap(),
            Value::from(5)
        );

        let msg = Value::deserialize(WeirdDe(Mode::Nothing))
            .unwrap_err()
            .to_string();
        assert!(msg.contains("a valid CBOR item"), "{msg}");
    }
}

#[test]
fn every_width_rejects_wrong_input() {
    // Each numeric entry point propagates its own conversion failure.
    assert!(Value::Null.deserialized::<i8>().is_err());
    assert!(Value::Null.deserialized::<i16>().is_err());
    assert!(Value::Null.deserialized::<i32>().is_err());
    assert!(Value::Null.deserialized::<i64>().is_err());
    assert!(Value::Null.deserialized::<i128>().is_err());
    assert!(Value::Null.deserialized::<u16>().is_err());
    assert!(Value::Null.deserialized::<u32>().is_err());
    assert!(Value::Null.deserialized::<u64>().is_err());
    assert!(Value::Null.deserialized::<u128>().is_err());
}

#[test]
fn nested_errors_propagate_through_value() {
    // Element failures surface through arrays, maps, enums and tags.
    let array = Value::Array(vec![Value::Null]);
    assert!(array.deserialized::<Vec<u8>>().is_err());

    let map = cbor!({"k" => null}).unwrap();
    assert!(map.deserialized::<BTreeMap<String, u8>>().is_err());
    let map = Value::Map(vec![(Value::Null, Value::from(1))]);
    assert!(map.deserialized::<BTreeMap<String, u8>>().is_err());

    let newtype = cbor!({"Newtype" => null}).unwrap();
    assert!(newtype.deserialized::<Enum>().is_err());
    let tuple = cbor!({"Tuple" => [1, null]}).unwrap();
    assert!(tuple.deserialized::<Enum>().is_err());
    let strukt = cbor!({"Struct" => {"x" => null}}).unwrap();
    assert!(strukt.deserialized::<Enum>().is_err());

    let tagged_garbage = Value::Tag(9, Box::new(Value::from(1)));
    assert!(tagged_garbage.deserialized::<Enum>().is_err());

    let some_garbage = Value::from("x");
    assert!(some_garbage.deserialized::<Option<u8>>().is_err());
}

#[test]
fn unserializable_values_fail_inside_every_container() {
    struct Boom;

    impl Serialize for Boom {
        fn serialize<S: serde::Serializer>(&self, _: S) -> Result<S::Ok, S::Error> {
            Err(serde::ser::Error::custom("boom"))
        }
    }

    // Sequences, tuples and tuple structs.
    assert!(Value::serialized(&vec![Boom]).is_err());
    assert!(Value::serialized(&(1u8, Boom)).is_err());
    struct T(u8, Boom);
    impl Serialize for T {
        fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            use serde::ser::SerializeTupleStruct;
            let mut acc = serializer.serialize_tuple_struct("T", 2)?;
            acc.serialize_field(&self.0)?;
            acc.serialize_field(&self.1)?;
            acc.end()
        }
    }
    assert!(Value::serialized(&T(1, Boom)).is_err());

    // Maps: in the key and in the value.
    struct BoomKeyMap;
    impl Serialize for BoomKeyMap {
        fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            use serde::ser::SerializeMap;
            let mut acc = serializer.serialize_map(Some(1))?;
            acc.serialize_key(&Boom)?;
            acc.serialize_value(&1u8)?;
            acc.end()
        }
    }
    assert!(Value::serialized(&BoomKeyMap).is_err());
    assert!(Value::serialized(&BTreeMap::from([(1u8, Boom)])).is_err());

    // Structs and each enum variant shape.
    struct S {
        x: Boom,
    }
    impl Serialize for S {
        fn serialize<S2: serde::Serializer>(&self, serializer: S2) -> Result<S2::Ok, S2::Error> {
            use serde::ser::SerializeStruct;
            let mut acc = serializer.serialize_struct("S", 1)?;
            acc.serialize_field("x", &self.x)?;
            acc.end()
        }
    }
    assert!(Value::serialized(&S { x: Boom }).is_err());

    enum E {
        Newtype(Boom),
        Tuple(Boom),
        Struct(Boom),
    }
    impl Serialize for E {
        fn serialize<S2: serde::Serializer>(&self, serializer: S2) -> Result<S2::Ok, S2::Error> {
            use serde::ser::{SerializeStructVariant, SerializeTupleVariant};
            match self {
                E::Newtype(b) => serializer.serialize_newtype_variant("E", 0, "N", b),
                E::Tuple(b) => {
                    let mut acc = serializer.serialize_tuple_variant("E", 1, "T", 1)?;
                    acc.serialize_field(b)?;
                    acc.end()
                }
                E::Struct(b) => {
                    let mut acc = serializer.serialize_struct_variant("E", 2, "S", 1)?;
                    acc.serialize_field("x", b)?;
                    acc.end()
                }
            }
        }
    }
    assert!(Value::serialized(&E::Newtype(Boom)).is_err());
    assert!(Value::serialized(&E::Tuple(Boom)).is_err());
    assert!(Value::serialized(&E::Struct(Boom)).is_err());

    // The tagged protocol with a good tag number and a failing payload.
    assert!(Value::serialized(&cbor::tag::AllowAny(Some(1), Boom)).is_err());
    // The untagged protocol with a failing payload.
    assert!(Value::serialized(&cbor::tag::AllowAny(None, Boom)).is_err());

    // Value::Array and Value::Map serialized into a failing serializer:
    // the container headers themselves are rejected.
    struct FW;
    impl std::io::Write for FW {
        fn write(&mut self, _: &[u8]) -> std::io::Result<usize> {
            Err(std::io::Error::other("x"))
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }
    assert!(cbor::to_writer(&Value::Array(vec![]), FW).is_err());
    assert!(cbor::to_writer(&Value::Map(vec![]), FW).is_err());

    // A failing key inside the *streaming* serializer's map path.
    assert!(cbor::to_vec(&BoomKeyMap).is_err());
}

#[test]
fn enum_variant_names_must_be_valid() {
    // The bare-text form with an unknown variant name.
    assert!(Value::from("Bogus").deserialized::<Enum>().is_err());
    // The map form with an unknown or non-string variant key.
    assert!(cbor!({"Bogus" => 1})
        .unwrap()
        .deserialized::<Enum>()
        .is_err());
    assert!(cbor!({5 => 1}).unwrap().deserialized::<Enum>().is_err());
    // A struct whose field name is not a string.
    let map = Value::Map(vec![(Value::Null, Value::from(1))]);
    assert!(map.deserialized::<Plain>().is_err());
}

// A misbehaving Serialize that emits a map value with no preceding key;
// the serializer must report an error rather than panic.
struct ValueWithoutKey;

impl Serialize for ValueWithoutKey {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeMap;
        let mut acc = serializer.serialize_map(Some(1))?;
        acc.serialize_value(&1u8)?;
        acc.end()
    }
}

#[test]
fn map_value_without_key_is_an_error() {
    let err = Value::serialized(&ValueWithoutKey).unwrap_err();
    assert!(
        err.to_string()
            .contains("serialize_value called before serialize_key"),
        "{err}"
    );
}
