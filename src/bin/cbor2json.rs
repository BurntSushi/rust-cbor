#![feature(exit_status, io)]

extern crate cbor;
extern crate "rustc-serialize" as rustc_serialize;

use std::env::set_exit_status;
use std::io::{self, Write};

use cbor::Decoder;
use rustc_serialize::json::ToJson;

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
    let mut dec = Decoder::from_reader(io::stdin());
    let cbor = match dec.items().next() {
        None => { return; },
        Some(result) => ordie!(result),
    };
    let json = cbor.to_json().pretty().to_string();
    print!("{}", json);
}
