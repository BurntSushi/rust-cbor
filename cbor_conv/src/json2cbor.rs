use std::io::{self, BufReader, Write};
use std::process;

// Reads a stream of JSON values from stdin and writes each of them to
// stdout as a CBOR item, incrementally.
fn main() {
    if let Err(err) = run() {
        eprintln!("json2cbor: {err}");
        process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let stdin = BufReader::new(io::stdin().lock());
    let stdout = io::stdout();
    let mut stdout = stdout.lock();

    for value in serde_json::Deserializer::from_reader(stdin).into_iter::<serde_json::Value>() {
        cbor::to_writer(&value?, &mut stdout)?;
    }

    Ok(stdout.flush()?)
}
