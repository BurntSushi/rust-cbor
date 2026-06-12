//! Tests for the dynamic `Value` type and the `cbor!` macro.

use cbor::{cbor, Value};
use serde::{Deserialize, Serialize};

#[test]
fn macro_builds_values() {
    let value = cbor!({
        "code" => 415,
        "message" => null,
        "continue" => false,
        "extra" => { "numbers" => [8.2341e+4, 0.251425] },
    })
    .unwrap();

    let map = value.as_map().unwrap();
    assert_eq!(map.len(), 4);
    assert_eq!(map[0], (Value::from("code"), Value::from(415)));
    assert_eq!(map[1], (Value::from("message"), Value::Null));
    assert_eq!(map[2], (Value::from("continue"), Value::from(false)));

    let extra = map[3].1.as_map().unwrap();
    assert_eq!(
        extra[0],
        (
            Value::from("numbers"),
            Value::Array(vec![Value::from(8.2341e+4), Value::from(0.251425)])
        )
    );
}

#[test]
fn macro_inlines_expressions() {
    let x = 21u8 * 2;
    let value = cbor!([x, { "nested" => [x] }, "tail"]).unwrap();
    assert_eq!(
        value,
        Value::Array(vec![
            Value::from(42),
            Value::Map(vec![(
                Value::from("nested"),
                Value::Array(vec![Value::from(42)])
            )]),
            Value::from("tail"),
        ])
    );
}

#[derive(Debug, PartialEq, Deserialize, Serialize)]
struct Point {
    x: i32,
    y: i32,
}

#[test]
fn serialized_and_deserialized() {
    let point = Point { x: 1, y: -2 };

    let value = Value::serialized(&point).unwrap();
    assert_eq!(value, cbor!({ "x" => 1, "y" => -2 }).unwrap());

    let back: Point = value.deserialized().unwrap();
    assert_eq!(back, point);
}

#[test]
fn value_through_the_wire() {
    let value = cbor!({
        "integers" => [0, -1, u64::MAX, i128::from(u64::MAX) + 1],
        "floats" => [0.5, f64::INFINITY],
        "null" => null,
        1 => "non-string keys",
    })
    .unwrap();

    let bytes = cbor::to_vec(&value).unwrap();
    let back: Value = cbor::from_slice(&bytes).unwrap();
    assert_eq!(back, value);
}

#[test]
fn accessors() {
    let value = Value::from("hello");
    assert!(value.is_text());
    assert_eq!(value.as_text(), Some("hello"));
    assert_eq!(value.into_text().unwrap(), "hello");

    let value = Value::from(3.5);
    assert!(value.is_float());
    assert_eq!(value.as_float(), Some(3.5));

    let value = Value::from(17);
    assert_eq!(u8::try_from(value.as_integer().unwrap()).unwrap(), 17);

    let mut value = Value::Array(vec![Value::Null]);
    value.as_array_mut().unwrap().push(Value::from(true));
    assert_eq!(value.as_array().unwrap().len(), 2);

    let value = Value::Tag(1, Box::new(Value::from(0)));
    assert_eq!(value.as_tag().unwrap().0, 1);
    assert!(Value::Null.is_null());
    assert!(!Value::from(false).into_bool().unwrap());
    assert_eq!(Value::from(&b"ab"[..]).into_bytes().unwrap(), b"ab");

    // The failure mode returns the original value.
    assert_eq!(Value::from(1).into_text().unwrap_err(), Value::from(1));
}

#[test]
fn from_128_bit_integers() {
    assert_eq!(Value::from(1u128), Value::from(1));
    assert_eq!(Value::from(-1i128), Value::from(-1));

    let value = Value::from(u128::MAX);
    let (tag, inner) = value.as_tag().unwrap();
    assert_eq!(tag, 2);
    assert_eq!(inner.as_bytes().unwrap().len(), 16);

    let value = Value::from(i128::MIN);
    let (tag, inner) = value.as_tag().unwrap();
    assert_eq!(tag, 3);
    assert_eq!(inner.as_bytes().unwrap().len(), 16);

    // And back out through deserialized().
    assert_eq!(
        Value::from(u128::MAX).deserialized::<u128>().unwrap(),
        u128::MAX
    );
    assert_eq!(
        Value::from(i128::MIN).deserialized::<i128>().unwrap(),
        i128::MIN
    );
}
