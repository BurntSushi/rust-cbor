use rustc_serialize::Encodable;
use rustc_serialize::Encoder as RustcEncoder;

use {
    CborResult, CborError,
};

pub trait CborEncodable {
    fn cbor_encode<W: Writer>(&self, e: &mut Encoder<W>) -> CborResult<()>;
}

impl<E: Encodable> CborEncodable for E {
    fn cbor_encode<W: Writer>(&self, e: &mut Encoder<W>) -> CborResult<()> {
        self.encode(e)
    }
}

pub struct Encoder<W> {
    wtr: W,
    emitting_key: bool,
}

impl<W: Writer> RustcEncoder for Encoder<W> {
    type Error = CborError;

    fn emit_nil(&mut self) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_usize(&mut self, v: usize) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_u64(&mut self, v: u64) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_u32(&mut self, v: u32) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_u16(&mut self, v: u16) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_u8(&mut self, v: u8) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_isize(&mut self, v: isize) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_i64(&mut self, v: i64) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_i32(&mut self, v: i32) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_i16(&mut self, v: i16) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_i8(&mut self, v: i8) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_f64(&mut self, v: f64) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_f32(&mut self, v: f32) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_bool(&mut self, v: bool) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_char(&mut self, v: char) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_str(&mut self, v: &str) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_enum<F>(&mut self, name: &str, f: F) -> CborResult<()>
            where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_enum_variant<F>(
        &mut self,
        v_name: &str,
        v_id: usize,
        len: usize,
        f: F,
    ) -> CborResult<()>
    where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_enum_variant_arg<F>(&mut self, idx: usize, f: F) -> CborResult<()>
            where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_enum_struct_variant<F>(
        &mut self,
        v_name: &str,
        v_id: usize,
        len: usize,
        f: F,
    ) -> CborResult<()>
    where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_enum_struct_variant_field<F>(
        &mut self,
        f_name: &str,
        idx: usize,
        f: F,
    ) -> CborResult<()>
    where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_struct<F>(
        &mut self,
        name: &str,
        len: usize,
        f: F,
    ) -> CborResult<()>
    where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_struct_field<F>(
        &mut self,
        f_name: &str,
        f_idx: usize,
        f: F,
    ) -> CborResult<()>
    where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_tuple<F>(&mut self, len: usize, f: F) -> CborResult<()>
            where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_tuple_arg<F>(&mut self, idx: usize, f: F) -> CborResult<()>
            where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_tuple_struct<F>(
        &mut self,
        name: &str,
        len: usize,
        f: F,
    ) -> CborResult<()>
    where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_tuple_struct_arg<F>(&mut self, idx: usize, f: F) -> CborResult<()>
            where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_option<F>(&mut self, f: F) -> CborResult<()>
            where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_option_none(&mut self) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_option_some<F>(&mut self, f: F) -> CborResult<()>
            where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_seq<F>(&mut self, len: usize, f: F) -> CborResult<()>
            where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_seq_elt<F>(&mut self, idx: usize, f: F) -> CborResult<()>
            where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_map<F>(&mut self, len: usize, f: F) -> CborResult<()>
            where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_map_elt_key<F>(&mut self, idx: usize, f: F) -> CborResult<()>
            where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        unimplemented!()
    }

    fn emit_map_elt_val<F>(&mut self, idx: usize, f: F) -> CborResult<()>
            where F: FnOnce(&mut Encoder<W>) -> CborResult<()> {
        unimplemented!()
    }
}
