use std::fmt::Write as _;
use std::io::{self, BufReader, Write};
use std::process;

use cbor::Value;

// Reads a stream of CBOR items from stdin and writes each of them to
// stdout as a pretty-printed JSON value.
//
// CBOR constructs that have no JSON equivalent are converted as follows:
// byte strings become lowercase hex strings, non-string map keys are
// JSON-encoded into strings, non-finite floats become null, tags are
// dropped (the inner value is kept) and the "undefined" simple value
// becomes null.
fn main() {
    if let Err(err) = run() {
        eprintln!("cbor2json: {err}");
        process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let stdin = BufReader::new(io::stdin().lock());
    let stdout = io::stdout();
    let mut stdout = stdout.lock();

    for item in cbor::de::Deserializer::from_reader(stdin).into_iter::<Value>() {
        let json = to_json(item?);
        serde_json::to_writer_pretty(&mut stdout, &json)?;
        stdout.write_all(b"\n")?;
    }

    Ok(stdout.flush()?)
}

fn to_json(value: Value) -> serde_json::Value {
    use serde_json::Value as Json;

    match value {
        Value::Null => Json::Null,
        Value::Bool(x) => Json::Bool(x),
        Value::Integer(x) => match (u64::try_from(x), i64::try_from(x)) {
            (Ok(x), _) => Json::from(x),
            (_, Ok(x)) => Json::from(x),
            // Outside both ranges (e.g. near -2^64): fall back to a string.
            _ => Json::String(i128::from(x).to_string()),
        },
        Value::Float(x) => serde_json::Number::from_f64(x).map_or(Json::Null, Json::Number),
        Value::Bytes(x) => Json::String(hex(&x)),
        Value::Text(x) => Json::String(x),
        Value::Tag(_, x) => to_json(*x),
        Value::Array(x) => Json::Array(x.into_iter().map(to_json).collect()),
        Value::Map(x) => Json::Object(
            x.into_iter()
                .map(|(k, v)| {
                    let key = match k {
                        Value::Text(s) => s,
                        // Serializing a serde_json::Value to a string cannot
                        // fail; never fall back to an (ambiguous) empty key.
                        other => serde_json::to_string(&to_json(other))
                            .expect("serializing a JSON value cannot fail"),
                    };
                    (key, to_json(v))
                })
                .collect(),
        ),
        _ => Json::Null,
    }
}

fn hex(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        let _ = write!(out, "{b:02x}");
    }
    out
}
