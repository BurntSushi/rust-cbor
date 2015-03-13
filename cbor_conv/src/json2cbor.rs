#![feature(exit_status, io)]

extern crate cbor;
extern crate "rustc-serialize" as rustc_serialize;

use std::env::set_exit_status;
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
                Err(err) => { err!("{}", err); set_exit_status(1); return; }
            }
        );
    }
    let json = ordie!(Json::from_reader(&mut io::stdin()));
    let mut enc = Encoder::from_writer(io::stdout());
    ordie!(enc.encode(&[json.to_cbor()]));
}
