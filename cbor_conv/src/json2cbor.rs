extern crate cbor;
extern crate rustc_serialize;

use std::io::{self, Write};

use cbor::{Encoder, ToCbor};
use rustc_serialize::json::Json;

macro_rules! err {
    ($($arg:tt)*) => ({ let _ = writeln!(&mut io::stderr(), $($arg)*); });
}

fn main() {
    macro_rules! ordie {
        ($e:expr) => (
            match $e {
                Ok(v) => v,
                Err(err) => { err!("{}", err); ::std::process::exit(1); }
            }
        );
    }
    let json = ordie!(Json::from_reader(&mut io::stdin()));
    let mut enc = Encoder::from_writer(io::stdout());
    ordie!(enc.encode(&[json.to_cbor()]));
}
