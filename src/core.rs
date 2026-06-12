//! Low-level CBOR encoding and decoding.
//!
//! This module provides a pull/push interface over CBOR item *headers*
//! (RFC 8949 §3). A CBOR item on the wire consists of a one-byte prefix
//! (major type + additional information), an optional multi-byte argument,
//! and an optional body (for bytes, text, arrays, maps and tags).
//!
//! [`Decoder::pull`] reads the next header from the input and
//! [`Encoder::push`] writes a header to the output. Item bodies are read and
//! written directly through the underlying reader/writer; helper methods are
//! provided for (possibly segmented) byte and text strings.
//!
//! Most users should prefer the serde interface in the crate root or the
//! dynamic [`Value`](crate::Value) type; this module is for applications
//! that need precise control over the wire format.

use std::io::{Read, Write};

/// Simple value constants (RFC 8949 §3.3).
pub mod simple {
    /// Simple value 20: `false`.
    pub const FALSE: u8 = 20;
    /// Simple value 21: `true`.
    pub const TRUE: u8 = 21;
    /// Simple value 22: `null`.
    pub const NULL: u8 = 22;
    /// Simple value 23: `undefined`.
    pub const UNDEFINED: u8 = 23;
}

/// Well-known tag constants (RFC 8949 §3.4).
pub mod tag {
    /// Tag 2: an unsigned bignum encoded as a byte string.
    pub const BIGPOS: u64 = 2;
    /// Tag 3: a negative bignum encoded as a byte string.
    pub const BIGNEG: u64 = 3;
}

/// An error that occurred while reading or writing CBOR items.
#[derive(Debug)]
pub enum Error {
    /// An error from the underlying reader or writer.
    Io(std::io::Error),

    /// The input is not well-formed CBOR.
    ///
    /// Contains the byte offset of the offending item.
    Syntax(usize),
}

impl From<std::io::Error> for Error {
    #[inline]
    fn from(value: std::io::Error) -> Self {
        Self::Io(value)
    }
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Error::Io(err) => write!(f, "i/o error: {err}"),
            Error::Syntax(offset) => write!(f, "syntax error at offset {offset}"),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Error::Io(err) => Some(err),
            Error::Syntax(..) => None,
        }
    }
}

/// A semantic representation of a CBOR item header.
///
/// A header carries the major type and the argument of an item. It does
/// **not** carry the body: after pulling a [`Header::Bytes`], for example,
/// the byte string itself still has to be read from the decoder.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Header {
    /// An unsigned integer (major type 0).
    Positive(u64),

    /// A negative integer (major type 1).
    ///
    /// The value carried here is the encoded argument, i.e. the bits of the
    /// represented number `-1 - n` with all bits inverted. To recover the
    /// numeric value: `n as i128 ^ !0`.
    Negative(u64),

    /// A floating-point value (major type 7, additional information 25-27).
    Float(f64),

    /// A simple value (major type 7).
    ///
    /// Values 24 to 31 (inclusive) are reserved by RFC 8949 §3.3 and have no
    /// well-formed encoding; pushing such a header produces output that any
    /// conforming decoder (including this one) rejects.
    Simple(u8),

    /// A tag (major type 6).
    Tag(u64),

    /// The "break" stop code terminating an indefinite-length item.
    Break,

    /// A byte string (major type 2).
    ///
    /// `None` indicates an indefinite-length byte string composed of
    /// definite-length segments terminated by [`Header::Break`].
    Bytes(Option<usize>),

    /// A text string (major type 3); the length is in bytes.
    ///
    /// `None` indicates an indefinite-length text string composed of
    /// definite-length segments terminated by [`Header::Break`].
    Text(Option<usize>),

    /// An array (major type 4); the length is in items.
    ///
    /// `None` indicates an indefinite-length array terminated by
    /// [`Header::Break`].
    Array(Option<usize>),

    /// A map (major type 5); the length is in key/value *pairs*.
    ///
    /// `None` indicates an indefinite-length map terminated by
    /// [`Header::Break`].
    Map(Option<usize>),
}

// The encoded argument of a header: the low 5 bits of the prefix byte plus
// 0, 1, 2, 4 or 8 following bytes.
enum Arg {
    This(u8),   // immediate (0..=23)
    Next1(u8),  // additional information 24
    Next2(u16), // additional information 25
    Next4(u32), // additional information 26
    Next8(u64), // additional information 27
    Indefinite, // additional information 31
}

impl Header {
    // Split a header into its major type and encoded argument.
    fn into_parts(self) -> (u8, Arg) {
        let int = |x: u64| match x {
            x if x <= 23 => Arg::This(x as u8),
            x if x <= u8::MAX as u64 => Arg::Next1(x as u8),
            x if x <= u16::MAX as u64 => Arg::Next2(x as u16),
            x if x <= u32::MAX as u64 => Arg::Next4(x as u32),
            x => Arg::Next8(x),
        };

        let len = |x: Option<usize>| x.map(|n| int(n as u64)).unwrap_or(Arg::Indefinite);

        match self {
            Header::Positive(x) => (0, int(x)),
            Header::Negative(x) => (1, int(x)),
            Header::Bytes(x) => (2, len(x)),
            Header::Text(x) => (3, len(x)),
            Header::Array(x) => (4, len(x)),
            Header::Map(x) => (5, len(x)),
            Header::Tag(x) => (6, int(x)),
            Header::Break => (7, Arg::Indefinite),

            Header::Simple(x) => match x {
                0..=23 => (7, Arg::This(x)),
                x => (7, Arg::Next1(x)),
            },

            Header::Float(x) => match f64_to_f16(x) {
                Some(n16) => (7, Arg::Next2(n16)),
                None => {
                    let n32 = x as f32;
                    if (n32 as f64).to_bits() == x.to_bits() {
                        (7, Arg::Next4(n32.to_bits()))
                    } else {
                        (7, Arg::Next8(x.to_bits()))
                    }
                }
            },
        }
    }
}

/// An encoder for serializing CBOR items.
///
/// All output is written through to the wrapped writer; consider providing
/// a buffered writer for performance.
pub struct Encoder<W>(W);

impl<W: Write> From<W> for Encoder<W> {
    #[inline]
    fn from(writer: W) -> Self {
        Self(writer)
    }
}

impl<W: Write> Encoder<W> {
    /// Writes a single header to the output.
    pub fn push(&mut self, header: Header) -> std::io::Result<()> {
        let (major, arg) = header.into_parts();

        let mut buffer = [0u8; 9];
        let n = match arg {
            Arg::This(x) => {
                buffer[0] = major << 5 | x;
                1
            }
            Arg::Indefinite => {
                buffer[0] = major << 5 | 31;
                1
            }
            Arg::Next1(x) => {
                buffer[0] = major << 5 | 24;
                buffer[1] = x;
                2
            }
            Arg::Next2(x) => {
                buffer[0] = major << 5 | 25;
                buffer[1..3].copy_from_slice(&x.to_be_bytes());
                3
            }
            Arg::Next4(x) => {
                buffer[0] = major << 5 | 26;
                buffer[1..5].copy_from_slice(&x.to_be_bytes());
                5
            }
            Arg::Next8(x) => {
                buffer[0] = major << 5 | 27;
                buffer[1..9].copy_from_slice(&x.to_be_bytes());
                9
            }
        };

        self.0.write_all(&buffer[..n])
    }

    /// Writes a definite-length byte string (header and body).
    pub fn bytes(&mut self, value: &[u8]) -> std::io::Result<()> {
        self.push(Header::Bytes(Some(value.len())))?;
        self.0.write_all(value)
    }

    /// Writes a definite-length text string (header and body).
    pub fn text(&mut self, value: &str) -> std::io::Result<()> {
        self.push(Header::Text(Some(value.len())))?;
        self.0.write_all(value.as_bytes())
    }

    /// Writes raw bytes directly to the output.
    ///
    /// This is used to write item bodies after pushing the corresponding
    /// header.
    #[inline]
    pub fn write_all(&mut self, data: &[u8]) -> std::io::Result<()> {
        self.0.write_all(data)
    }

    /// Flushes the underlying writer.
    #[inline]
    pub fn flush(&mut self) -> std::io::Result<()> {
        self.0.flush()
    }
}

// Reading the body of a string item never trusts the declared length for
// allocation: memory grows as data actually arrives, in chunks of this size.
const CHUNK: usize = 16 * 1024;

/// A decoder for parsing CBOR items.
///
/// Input is read directly from the wrapped reader one item at a time;
/// consider providing a buffered reader for performance.
pub struct Decoder<R> {
    reader: R,
    offset: usize,
    pushback: Option<(Header, usize)>,
    mark: usize,
}

impl<R: Read> From<R> for Decoder<R> {
    #[inline]
    fn from(reader: R) -> Self {
        Self {
            reader,
            offset: 0,
            pushback: None,
            mark: 0,
        }
    }
}

impl<R: Read> Decoder<R> {
    /// Pulls the next header from the input.
    pub fn pull(&mut self) -> Result<Header, Error> {
        if let Some((header, end)) = self.pushback.take() {
            self.mark = self.offset;
            self.offset = end;
            return Ok(header);
        }

        let start = self.offset;
        self.mark = start;

        let mut prefix = [0u8; 1];
        self.read_exact(&mut prefix)?;

        let major = prefix[0] >> 5;
        let minor = prefix[0] & 0b00011111;

        let arg = match minor {
            x @ 0..=23 => Arg::This(x),
            24 => {
                let mut b = [0u8; 1];
                self.read_exact(&mut b)?;
                Arg::Next1(b[0])
            }
            25 => {
                let mut b = [0u8; 2];
                self.read_exact(&mut b)?;
                Arg::Next2(u16::from_be_bytes(b))
            }
            26 => {
                let mut b = [0u8; 4];
                self.read_exact(&mut b)?;
                Arg::Next4(u32::from_be_bytes(b))
            }
            27 => {
                let mut b = [0u8; 8];
                self.read_exact(&mut b)?;
                Arg::Next8(u64::from_be_bytes(b))
            }
            31 => Arg::Indefinite,
            _ => return Err(Error::Syntax(start)),
        };

        let int = |arg: Arg| match arg {
            Arg::This(x) => Some(x as u64),
            Arg::Next1(x) => Some(x as u64),
            Arg::Next2(x) => Some(x as u64),
            Arg::Next4(x) => Some(x as u64),
            Arg::Next8(x) => Some(x),
            Arg::Indefinite => None,
        };

        let len = |arg: Arg| match int(arg) {
            Some(x) => usize::try_from(x)
                .map(Some)
                .map_err(|_| Error::Syntax(start)),
            None => Ok(None),
        };

        Ok(match major {
            0 => Header::Positive(int(arg).ok_or(Error::Syntax(start))?),
            1 => Header::Negative(int(arg).ok_or(Error::Syntax(start))?),
            2 => Header::Bytes(len(arg)?),
            3 => Header::Text(len(arg)?),
            4 => Header::Array(len(arg)?),
            5 => Header::Map(len(arg)?),
            6 => Header::Tag(int(arg).ok_or(Error::Syntax(start))?),
            7 => match arg {
                Arg::This(x) => Header::Simple(x),
                // RFC 8949 §3.3: a 0xf8 prefix followed by a byte less than
                // 0x20 is not well-formed.
                Arg::Next1(x) if x >= 32 => Header::Simple(x),
                Arg::Next1(..) => return Err(Error::Syntax(start)),
                Arg::Next2(x) => Header::Float(f16_to_f64(x)),
                Arg::Next4(x) => Header::Float(f32::from_bits(x) as f64),
                Arg::Next8(x) => Header::Float(f64::from_bits(x)),
                Arg::Indefinite => Header::Break,
            },
            _ => unreachable!(),
        })
    }

    /// Pushes a header back into the decoder, to be returned by the next
    /// [`pull`](Self::pull).
    ///
    /// # Panics
    ///
    /// Panics if a header is already buffered. Only push back the header
    /// returned by the immediately preceding `pull`.
    pub fn push(&mut self, header: Header) {
        assert!(self.pushback.is_none(), "header already buffered");
        self.pushback = Some((header, self.offset));
        self.offset = self.mark;
    }

    /// Returns the byte offset of the next item in the stream.
    ///
    /// The offset starts at zero when the decoder is created.
    #[inline]
    pub fn offset(&self) -> usize {
        self.offset
    }

    /// Reads exactly `data.len()` bytes of an item body from the input.
    pub fn read_exact(&mut self, data: &mut [u8]) -> std::io::Result<()> {
        debug_assert!(self.pushback.is_none());
        self.reader.read_exact(data)?;
        self.offset += data.len();
        Ok(())
    }

    // Appends `len` body bytes to `out`, growing the buffer as data arrives
    // so that a forged length cannot trigger a huge allocation up front.
    fn read_body(&mut self, len: usize, out: &mut Vec<u8>) -> Result<(), Error> {
        let mut remaining = len;
        while remaining > 0 {
            let chunk = remaining.min(CHUNK);
            let used = out.len();
            out.resize(used + chunk, 0);
            self.read_exact(&mut out[used..])?;
            remaining -= chunk;
        }
        Ok(())
    }

    /// Reads the body of a byte string into `out`.
    ///
    /// Call this immediately after pulling a `Header::Bytes(len)`, passing
    /// the pulled `len`. Indefinite-length (segmented) byte strings are
    /// handled transparently.
    pub fn bytes_body(&mut self, len: Option<usize>, out: &mut Vec<u8>) -> Result<(), Error> {
        match len {
            Some(len) => self.read_body(len, out),
            None => loop {
                let offset = self.offset;
                match self.pull()? {
                    Header::Break => return Ok(()),
                    // Segments must be definite-length strings of the same
                    // major type (RFC 8949 §3.2.3).
                    Header::Bytes(Some(len)) => self.read_body(len, out)?,
                    _ => return Err(Error::Syntax(offset)),
                }
            },
        }
    }

    /// Reads the body of a text string into `out`.
    ///
    /// Call this immediately after pulling a `Header::Text(len)`, passing
    /// the pulled `len`. Indefinite-length (segmented) text strings are
    /// handled transparently; every segment must itself be valid UTF-8.
    pub fn text_body(&mut self, len: Option<usize>, out: &mut String) -> Result<(), Error> {
        let read_segment = |me: &mut Self, len: usize, out: &mut String| {
            let offset = me.offset;
            let mut buffer = Vec::new();
            me.read_body(len, &mut buffer)?;
            match String::from_utf8(buffer) {
                Ok(s) => {
                    out.push_str(&s);
                    Ok(())
                }
                Err(..) => Err(Error::Syntax(offset)),
            }
        };

        match len {
            Some(len) => read_segment(self, len, out),
            None => loop {
                let offset = self.offset;
                match self.pull()? {
                    Header::Break => return Ok(()),
                    Header::Text(Some(len)) => read_segment(self, len, out)?,
                    _ => return Err(Error::Syntax(offset)),
                }
            },
        }
    }
}

/// Converts IEEE 754 half-precision bits to an `f64`.
///
/// This follows the decoding algorithm given in RFC 8949 Appendix D.
pub fn f16_to_f64(bits: u16) -> f64 {
    let exp = (bits >> 10) & 0x1f;
    let frac = (bits & 0x3ff) as f64;

    let value = match exp {
        0 => frac * 2f64.powi(-24),
        31 if frac == 0.0 => f64::INFINITY,
        31 => f64::NAN,
        _ => (1024.0 + frac) * 2f64.powi(exp as i32 - 25),
    };

    if bits & 0x8000 == 0 {
        value
    } else {
        -value
    }
}

/// Converts an `f64` to IEEE 754 half-precision bits if (and only if) the
/// conversion is lossless. NaN converts to the canonical quiet NaN.
pub fn f64_to_f16(value: f64) -> Option<u16> {
    let bits = value.to_bits();
    let sign = ((bits >> 48) & 0x8000) as u16;
    let exp = ((bits >> 52) & 0x7ff) as i32;
    let frac = bits & 0x000f_ffff_ffff_ffff;

    let half = if exp == 0x7ff {
        // Infinity or NaN. Any NaN becomes the canonical quiet NaN; the
        // round-trip check below rejects NaNs whose payload would be lost.
        match frac {
            0 => sign | 0x7c00,
            _ => 0x7e00,
        }
    } else {
        let unbiased = exp - 1023;
        if exp == 0 && frac == 0 {
            sign // ±0.0
        } else if (-14..=15).contains(&unbiased) {
            // Candidate for an f16 normal: the low 42 fraction bits must
            // be zero for the conversion to be exact.
            if frac & ((1 << 42) - 1) != 0 {
                return None;
            }
            sign | (((unbiased + 15) as u16) << 10) | (frac >> 42) as u16
        } else if (-24..-14).contains(&unbiased) {
            // Candidate for an f16 subnormal.
            let mantissa = (1u64 << 52) | frac;
            let shift = 42 + (-14 - unbiased);
            if mantissa & ((1 << shift) - 1) != 0 {
                return None;
            }
            sign | (mantissa >> shift) as u16
        } else {
            return None;
        }
    };

    // Belt and braces: only report success on an exact bit-level round trip.
    if f16_to_f64(half).to_bits() == bits {
        Some(half)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Every f16 bit pattern must survive decoding to f64 and re-encoding.
    #[test]
    fn f16_exhaustive_roundtrip() {
        for bits in 0..=u16::MAX {
            let wide = f16_to_f64(bits);

            if wide.is_nan() {
                // NaN payloads are not preserved; the canonical NaN is.
                assert!(f64_to_f16(f64::NAN) == Some(0x7e00));
                continue;
            }

            assert_eq!(f64_to_f16(wide), Some(bits), "bits {bits:04x} ({wide})");
        }
    }

    // Values that are not representable as f16 must be rejected.
    #[test]
    fn f16_rejects_lossy() {
        for value in [
            f64::MIN_POSITIVE, // far below the subnormal range
            65504.0 + 32.0,    // above f16::MAX
            65536.0,           // 2^16, exponent out of range
            1.1,               // fraction bits beyond 10
            5.960464477539063e-8 / 2.0,
        ] {
            assert_eq!(f64_to_f16(value), None, "{value}");
        }
    }

    // Headers round-trip through encode and decode.
    #[test]
    fn header_roundtrip() {
        let headers = [
            Header::Positive(0),
            Header::Positive(23),
            Header::Positive(24),
            Header::Positive(u64::MAX),
            Header::Negative(0),
            Header::Negative(u64::MAX),
            Header::Float(1.5),
            Header::Float(f64::MAX),
            Header::Simple(simple::FALSE),
            Header::Simple(simple::UNDEFINED),
            Header::Simple(255),
            Header::Tag(0),
            Header::Tag(u64::MAX),
            Header::Break,
            Header::Bytes(Some(0)),
            Header::Bytes(Some(usize::MAX)),
            Header::Bytes(None),
            Header::Text(Some(64)),
            Header::Text(None),
            Header::Array(Some(1)),
            Header::Array(None),
            Header::Map(Some(1)),
            Header::Map(None),
        ];

        for header in headers {
            let mut buffer = Vec::new();
            Encoder::from(&mut buffer).push(header).unwrap();

            let mut decoder = Decoder::from(&buffer[..]);
            assert_eq!(decoder.pull().unwrap(), header, "{header:?}");
            assert_eq!(decoder.offset(), buffer.len());
        }
    }

    // Pushback rewinds the offset and replays the header.
    #[test]
    fn pushback() {
        let bytes = [0x19, 0x01, 0x00, 0x01]; // 256, 1
        let mut decoder = Decoder::from(&bytes[..]);

        let first = decoder.pull().unwrap();
        assert_eq!(first, Header::Positive(256));
        assert_eq!(decoder.offset(), 3);

        decoder.push(first);
        assert_eq!(decoder.offset(), 0);

        assert_eq!(decoder.pull().unwrap(), Header::Positive(256));
        assert_eq!(decoder.offset(), 3);
        assert_eq!(decoder.pull().unwrap(), Header::Positive(1));
        assert_eq!(decoder.offset(), 4);
    }
}
