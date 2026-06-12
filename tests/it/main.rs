//! The single integration-test binary.
//!
//! Keeping all integration tests in one binary makes `cargo test` faster
//! and lets the coverage of generic functions instantiated by the tests
//! merge properly.

mod canonical;
mod de_edge;
mod errors;
mod limits;
mod rfc8949;
mod roundtrip;
mod tag;
mod value;
mod value_api;
mod value_serde;
