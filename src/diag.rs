//! CBOR diagnostic notation (RFC 8949 §8).
//!
//! Diagnostic notation is a human-readable, JSON-like text form of CBOR
//! meant for documentation and debugging; it is produced, never parsed.
//! The output of this module matches the diagnostic column of RFC 8949
//! Appendix A exactly, including the extended forms of §8.1: the `_`
//! marker for indefinite-length items and `(_ ...)` for segmented
//! strings.

use std::fmt::Write as _;
use std::io::Read;

use crate::core::{simple, tag, Decoder, Header};
use crate::de::{expect_eof, Error, DEFAULT_RECURSION_LIMIT};
use crate::value::Value;

/// Renders one CBOR item from a reader in diagnostic notation
/// (RFC 8949 §8).
///
/// Working directly on the wire preserves details that a decoded
/// [`Value`] cannot represent: indefinite-length items are rendered with
/// the `_` marker of §8.1 (`[_ 1, 2]`, `{_ "k": 1}`, `(_ h'01', h'02')`),
/// `undefined` and unassigned simple values appear as themselves, and
/// bignums (tags 2 and 3) are written as plain integers, exactly as in
/// RFC 8949 Appendix A.
///
/// The output is pure ASCII: non-ASCII text is escaped with `\uXXXX`
/// (using surrogate pairs beyond the basic plane), in the style of the
/// Appendix A examples. Like [`validate`](crate::validate), this checks
/// the input for well-formedness as it goes, requires the input to end
/// after the item, and bounds nesting by
/// [`DEFAULT_RECURSION_LIMIT`].
///
/// ```rust
/// let bytes = hex::decode("bf61610161629f0203ffff").unwrap();
/// assert_eq!(
///     cbor::diagnostic(&bytes[..]).unwrap(),
///     r#"{_ "a": 1, "b": [_ 2, 3]}"#
/// );
/// ```
pub fn diagnostic<R: Read>(reader: R) -> Result<String, Error> {
    let mut decoder = Decoder::from(reader);
    let mut out = String::new();
    item(&mut decoder, &mut out, DEFAULT_RECURSION_LIMIT)?;
    expect_eof(&mut decoder)?;
    Ok(out)
}

fn item<R: Read>(decoder: &mut Decoder<R>, out: &mut String, depth: usize) -> Result<(), Error> {
    let offset = decoder.offset();
    let header = decoder.pull()?;
    item_header(decoder, header, out, offset, depth)
}

fn item_header<R: Read>(
    decoder: &mut Decoder<R>,
    header: Header,
    out: &mut String,
    offset: usize,
    depth: usize,
) -> Result<(), Error> {
    if depth == 0 {
        return Err(Error::RecursionLimitExceeded);
    }

    match header {
        Header::Positive(x) => {
            let _ = write!(out, "{x}");
            Ok(())
        }

        Header::Negative(x) => {
            let _ = write!(out, "{}", -1 - i128::from(x));
            Ok(())
        }

        Header::Float(x) => {
            write_float(out, x);
            Ok(())
        }

        Header::Simple(simple::FALSE) => {
            out.push_str("false");
            Ok(())
        }
        Header::Simple(simple::TRUE) => {
            out.push_str("true");
            Ok(())
        }
        Header::Simple(simple::NULL) => {
            out.push_str("null");
            Ok(())
        }
        Header::Simple(simple::UNDEFINED) => {
            out.push_str("undefined");
            Ok(())
        }
        Header::Simple(x) => {
            let _ = write!(out, "simple({x})");
            Ok(())
        }

        Header::Break => Err(Error::Syntax(offset)),

        // Bignums render as plain integers, like in Appendix A; any other
        // payload falls back to the generic tag form.
        Header::Tag(t @ (tag::BIGPOS | tag::BIGNEG)) => {
            let offset = decoder.offset();
            match decoder.pull()? {
                Header::Bytes(len) => {
                    let mut payload = Vec::new();
                    decoder.bytes_body(len, &mut payload)?;
                    write_bignum(out, t == tag::BIGNEG, &payload);
                    Ok(())
                }
                header => {
                    let _ = write!(out, "{t}(");
                    item_header(decoder, header, out, offset, depth - 1)?;
                    out.push(')');
                    Ok(())
                }
            }
        }

        Header::Tag(t) => {
            let _ = write!(out, "{t}(");
            item(decoder, out, depth - 1)?;
            out.push(')');
            Ok(())
        }

        Header::Bytes(len) => match len {
            Some(len) => hex_segment(decoder, out, len),
            None => {
                out.push_str("(_ ");
                let mut first = true;
                loop {
                    let offset = decoder.offset();
                    match decoder.pull()? {
                        Header::Break => {
                            out.push(')');
                            return Ok(());
                        }
                        Header::Bytes(Some(len)) => {
                            if !first {
                                out.push_str(", ");
                            }
                            first = false;
                            hex_segment(decoder, out, len)?;
                        }
                        _ => return Err(Error::Syntax(offset)),
                    }
                }
            }
        },

        Header::Text(len) => match len {
            Some(len) => text_segment(decoder, out, len),
            None => {
                out.push_str("(_ ");
                let mut first = true;
                loop {
                    let offset = decoder.offset();
                    match decoder.pull()? {
                        Header::Break => {
                            out.push(')');
                            return Ok(());
                        }
                        Header::Text(Some(len)) => {
                            if !first {
                                out.push_str(", ");
                            }
                            first = false;
                            text_segment(decoder, out, len)?;
                        }
                        _ => return Err(Error::Syntax(offset)),
                    }
                }
            }
        },

        Header::Array(len) => match len {
            Some(len) => {
                out.push('[');
                for i in 0..len {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    item(decoder, out, depth - 1)?;
                }
                out.push(']');
                Ok(())
            }
            None => {
                out.push_str("[_ ");
                let mut first = true;
                loop {
                    let offset = decoder.offset();
                    match decoder.pull()? {
                        Header::Break => {
                            out.push(']');
                            return Ok(());
                        }
                        header => {
                            if !first {
                                out.push_str(", ");
                            }
                            first = false;
                            item_header(decoder, header, out, offset, depth - 1)?;
                        }
                    }
                }
            }
        },

        Header::Map(len) => match len {
            Some(len) => {
                out.push('{');
                for i in 0..len {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    item(decoder, out, depth - 1)?; // key
                    out.push_str(": ");
                    item(decoder, out, depth - 1)?; // value
                }
                out.push('}');
                Ok(())
            }
            None => {
                out.push_str("{_ ");
                let mut first = true;
                loop {
                    let offset = decoder.offset();
                    match decoder.pull()? {
                        Header::Break => {
                            out.push('}');
                            return Ok(());
                        }
                        header => {
                            if !first {
                                out.push_str(", ");
                            }
                            first = false;
                            item_header(decoder, header, out, offset, depth - 1)?; // key
                            out.push_str(": ");

                            // A break in place of a value leaves a dangling
                            // key, which is not well-formed (RFC 8949
                            // §5.3.1).
                            let offset = decoder.offset();
                            match decoder.pull()? {
                                Header::Break => return Err(Error::Syntax(offset)),
                                header => {
                                    item_header(decoder, header, out, offset, depth - 1)?;
                                }
                            }
                        }
                    }
                }
            }
        },
    }
}

// Renders a definite-length byte string as `h'..'`, reading the body in
// fixed-size chunks.
fn hex_segment<R: Read>(
    decoder: &mut Decoder<R>,
    out: &mut String,
    len: usize,
) -> Result<(), Error> {
    out.push_str("h'");

    let mut buffer = [0u8; 4096];
    let mut remaining = len;
    while remaining > 0 {
        let n = remaining.min(buffer.len());
        decoder.read_exact(&mut buffer[..n])?;
        remaining -= n;

        for b in &buffer[..n] {
            let _ = write!(out, "{b:02x}");
        }
    }

    out.push('\'');
    Ok(())
}

// Renders a definite-length text string as an escaped `".."` literal,
// reading the body in fixed-size chunks. Characters may straddle the
// chunk boundaries; up to three trailing bytes of an incomplete character
// carry over to the next chunk.
fn text_segment<R: Read>(
    decoder: &mut Decoder<R>,
    out: &mut String,
    len: usize,
) -> Result<(), Error> {
    let offset = decoder.offset();
    out.push('"');

    let mut buffer = [0u8; 4096];
    let mut carry = 0usize;
    let mut remaining = len;
    while remaining > 0 {
        let n = remaining.min(buffer.len() - carry);
        decoder.read_exact(&mut buffer[carry..carry + n])?;
        remaining -= n;
        let filled = carry + n;

        match core::str::from_utf8(&buffer[..filled]) {
            Ok(s) => {
                escape_into(out, s);
                carry = 0;
            }
            Err(err) => {
                // An incomplete character is only acceptable while more
                // body bytes are coming.
                if err.error_len().is_some() || remaining == 0 {
                    return Err(Error::Syntax(offset));
                }

                let valid = err.valid_up_to();
                let s = core::str::from_utf8(&buffer[..valid]).expect("prefix is valid UTF-8");
                escape_into(out, s);
                buffer.copy_within(valid..filled, 0);
                carry = filled - valid;
            }
        }
    }

    out.push('"');
    Ok(())
}

// Escapes text in the style of RFC 8949 Appendix A: like JSON, with all
// non-ASCII characters written as `\uXXXX` (surrogate pairs beyond the
// basic plane) so that the output is pure ASCII.
pub(crate) fn escape_into(out: &mut String, s: &str) {
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\u{08}' => out.push_str("\\b"),
            '\t' => out.push_str("\\t"),
            '\n' => out.push_str("\\n"),
            '\u{0c}' => out.push_str("\\f"),
            '\r' => out.push_str("\\r"),
            ' '..='~' => out.push(c),
            _ => {
                let mut units = [0u16; 2];
                for unit in c.encode_utf16(&mut units) {
                    let _ = write!(out, "\\u{unit:04x}");
                }
            }
        }
    }
}

// Renders a float as in RFC 8949 Appendix A: always with a decimal point
// or an exponent, plain decimal for moderate magnitudes and `d.ddde±x`
// otherwise, and the literals `Infinity`, `-Infinity` and `NaN`.
pub(crate) fn write_float(out: &mut String, x: f64) {
    if x.is_nan() {
        out.push_str("NaN");
        return;
    }
    if x.is_infinite() {
        out.push_str(if x < 0.0 { "-Infinity" } else { "Infinity" });
        return;
    }

    // The shortest representation that round-trips, as mantissa digits
    // and a decimal exponent.
    let shortest = format!("{x:e}");
    let (mantissa, exp) = shortest.split_once('e').expect("{:e} contains an exponent");
    let exp: i32 = exp.parse().expect("{:e} has an integer exponent");

    if let Some(digits) = mantissa.strip_prefix('-') {
        out.push('-');
        write_digits(out, digits, exp);
    } else {
        write_digits(out, mantissa, exp);
    }
}

// Writes the digits of `mantissa` ("d" or "d.ddd") scaled by `10^exp`.
fn write_digits(out: &mut String, mantissa: &str, exp: i32) {
    let mut digits = mantissa.as_bytes().iter().filter(|b| b.is_ascii_digit());
    let mut next = move || char::from(*digits.next().expect("mantissa has enough digits"));

    let count = mantissa.bytes().filter(u8::is_ascii_digit).count() as i32;

    if (-6..=20).contains(&exp) {
        if exp < 0 {
            // 0.0000ddd
            out.push_str("0.");
            for _ in exp..-1 {
                out.push('0');
            }
            for _ in 0..count {
                out.push(next());
            }
        } else {
            // dddd.ddd, zero-padded or split as needed
            for _ in 0..=exp.min(count - 1) {
                out.push(next());
            }
            for _ in count..=exp {
                out.push('0');
            }
            if count > exp + 1 {
                out.push('.');
                for _ in exp + 1..count {
                    out.push(next());
                }
            } else {
                out.push_str(".0");
            }
        }
    } else {
        // d.ddde±xx
        out.push(next());
        out.push('.');
        if count > 1 {
            for _ in 1..count {
                out.push(next());
            }
        } else {
            out.push('0');
        }
        let _ = write!(out, "e{}{}", if exp < 0 { '-' } else { '+' }, exp.abs());
    }
}

// Renders the payload of a bignum tag (2 or 3) as a decimal integer of
// arbitrary precision, as in RFC 8949 Appendix A. The represented value
// is the big-endian unsigned `payload` for tag 2 and `-1 - payload` for
// tag 3.
pub(crate) fn write_bignum(out: &mut String, negative: bool, payload: &[u8]) {
    let mut work: Vec<u8> = payload.iter().copied().skip_while(|&b| b == 0).collect();

    if negative {
        // Print -(n + 1): add one to the magnitude.
        let mut carry = true;
        for b in work.iter_mut().rev() {
            (*b, carry) = b.overflowing_add(1);
            if !carry {
                break;
            }
        }
        if carry {
            work.insert(0, 1);
        }
        out.push('-');
    } else if work.is_empty() {
        out.push('0');
        return;
    }

    // Repeated division by ten produces the decimal digits in reverse.
    let mut decimal = Vec::new();
    let mut start = 0;
    while start < work.len() {
        let mut rem = 0u32;
        for b in work[start..].iter_mut() {
            let cur = rem * 256 + u32::from(*b);
            *b = (cur / 10) as u8;
            rem = cur % 10;
        }
        decimal.push(b'0' + rem as u8);

        while start < work.len() && work[start] == 0 {
            start += 1;
        }
    }

    for digit in decimal.iter().rev() {
        out.push(char::from(*digit));
    }
}

// Renders a `Value` in diagnostic notation; backs `Display for Value`.
pub(crate) fn write_value(out: &mut String, value: &Value) {
    match value {
        Value::Integer(x) => {
            let _ = write!(out, "{}", i128::from(*x));
        }

        Value::Bytes(x) => {
            out.push_str("h'");
            for b in x {
                let _ = write!(out, "{b:02x}");
            }
            out.push('\'');
        }

        Value::Float(x) => write_float(out, *x),

        Value::Text(x) => {
            out.push('"');
            escape_into(out, x);
            out.push('"');
        }

        Value::Bool(false) => out.push_str("false"),
        Value::Bool(true) => out.push_str("true"),
        Value::Null => out.push_str("null"),

        Value::Tag(t @ (tag::BIGPOS | tag::BIGNEG), inner) => match inner.as_ref() {
            Value::Bytes(payload) => write_bignum(out, *t == tag::BIGNEG, payload),
            inner => {
                let _ = write!(out, "{t}(");
                write_value(out, inner);
                out.push(')');
            }
        },

        Value::Tag(t, inner) => {
            let _ = write!(out, "{t}(");
            write_value(out, inner);
            out.push(')');
        }

        Value::Array(items) => {
            out.push('[');
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                write_value(out, item);
            }
            out.push(']');
        }

        Value::Map(pairs) => {
            out.push('{');
            for (i, (key, val)) in pairs.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                write_value(out, key);
                out.push_str(": ");
                write_value(out, val);
            }
            out.push('}');
        }
    }
}
