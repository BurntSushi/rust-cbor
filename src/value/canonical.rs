//! Deterministic encoding support (RFC 8949 §4.2).

use serde::ser::Error as _;

use super::{Error, Integer, Value};

/// The map key ordering used by deterministic encoding.
///
/// RFC 8949 defines two deterministic key orderings. They agree whenever
/// all keys encode to the same length, but differ otherwise: for example,
/// `100` (`0x1864`) sorts after `-1` (`0x20`) bytewise, but before it
/// length-first.
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
#[non_exhaustive]
pub enum KeyOrder {
    /// Bytewise lexicographic order of the keys' deterministic encodings.
    ///
    /// This is the order required by the *core deterministic encoding
    /// requirements* (RFC 8949 §4.2.1) and is the recommended choice for
    /// new protocols; COSE (RFC 9052) and friends use it.
    #[default]
    Bytewise,

    /// Length-first order: keys with shorter encodings sort earlier, and
    /// keys of equal length sort bytewise.
    ///
    /// This is the "Canonical CBOR" ordering of RFC 7049 §3.9, kept in
    /// RFC 8949 §4.2.3 for backwards compatibility. Use it to interoperate
    /// with protocols and implementations built on the older rule (for
    /// example, `ciborium`'s canonical module).
    LengthFirst,
}

impl Value {
    /// Rewrites this value so that encoding it satisfies the *core
    /// deterministic encoding requirements* (RFC 8949 §4.2.1).
    ///
    /// This is [`canonicalize_with`](Self::canonicalize_with) using
    /// [`KeyOrder::Bytewise`].
    ///
    /// ```rust
    /// use cbor::{cbor, Value};
    ///
    /// let mut value = cbor!({ "z" => 1, "aa" => 2 }).unwrap();
    /// value.canonicalize().unwrap();
    ///
    /// // "z" (0x617a) sorts before "aa" (0x626161).
    /// let keys: Vec<_> = value.as_map().unwrap().iter().map(|(k, _)| k).collect();
    /// assert_eq!(keys, [&Value::from("z"), &Value::from("aa")]);
    /// ```
    #[inline]
    pub fn canonicalize(&mut self) -> Result<(), Error> {
        self.canonicalize_with(KeyOrder::Bytewise)
    }

    /// Rewrites this value so that encoding it is deterministic, sorting
    /// map keys in the given [`KeyOrder`].
    ///
    /// The encoder already emits preferred (smallest lossless)
    /// serializations and never produces indefinite-length items, so the
    /// work left to this method is normalizing the data model:
    ///
    /// * The entries of every map are sorted in `order`. Duplicate keys
    ///   are rejected with an error, since CBOR maps holding them are
    ///   invalid (RFC 8949 §5.6) and have no unique encoding.
    /// * Bignums (tags 2 and 3) are reduced to their preferred form:
    ///   leading zeros are stripped and values that fit in major type 0
    ///   or 1 become plain integers (RFC 8949 §3.4.3).
    /// * Every NaN is replaced by the canonical quiet NaN, so a single
    ///   floating-point value cannot have multiple encodings (RFC 8949
    ///   §4.2.2).
    ///
    /// ```rust
    /// use cbor::{cbor, KeyOrder, Value};
    ///
    /// let mut value = cbor!({ "aa" => 2, 100 => 1, -1 => 0 }).unwrap();
    /// value.canonicalize_with(KeyOrder::LengthFirst).unwrap();
    ///
    /// // -1 (0x20, one byte) sorts before 100 (0x1864, two bytes).
    /// let keys: Vec<_> = value.as_map().unwrap().iter().map(|(k, _)| k).collect();
    /// assert_eq!(keys, [&Value::from(-1), &Value::from(100), &Value::from("aa")]);
    /// ```
    pub fn canonicalize_with(&mut self, order: KeyOrder) -> Result<(), Error> {
        match self {
            Value::Float(x) if x.is_nan() => *x = f64::NAN,

            Value::Array(items) => {
                for item in items {
                    item.canonicalize_with(order)?;
                }
            }

            Value::Tag(tag @ (2 | 3), inner) => {
                inner.canonicalize_with(order)?;
                let tag = *tag;

                // Preferred serialization of a bignum: no leading zeros,
                // and major type 0/1 whenever the value fits.
                let reduced = match inner.as_mut() {
                    Value::Bytes(bytes) => {
                        let first = bytes.iter().position(|&b| b != 0).unwrap_or(bytes.len());
                        bytes.drain(..first);

                        if bytes.len() <= 8 {
                            let mut buffer = [0u8; 8];
                            buffer[8 - bytes.len()..].copy_from_slice(bytes);
                            let raw = u64::from_be_bytes(buffer);

                            Some(match tag {
                                2 => Integer::from(raw),
                                _ => Integer::try_from(-1i128 - i128::from(raw))
                                    .expect("-1 - u64 is always in range"),
                            })
                        } else {
                            None
                        }
                    }
                    _ => None,
                };

                if let Some(int) = reduced {
                    *self = Value::Integer(int);
                }
            }

            Value::Tag(.., inner) => inner.canonicalize_with(order)?,

            Value::Map(entries) => {
                let mut keyed = Vec::with_capacity(entries.len());
                for (mut key, mut val) in core::mem::take(entries) {
                    key.canonicalize_with(order)?;
                    val.canonicalize_with(order)?;

                    // Encoding a Value into a Vec cannot actually fail;
                    // the error mapping is purely defensive.
                    let encoded = crate::ser::to_vec(&key).map_err(Error::custom)?;
                    keyed.push((encoded, key, val));
                }

                keyed.sort_by(|a, b| match order {
                    KeyOrder::Bytewise => a.0.cmp(&b.0),
                    KeyOrder::LengthFirst => a.0.len().cmp(&b.0.len()).then_with(|| a.0.cmp(&b.0)),
                });

                // Equal keys are adjacent in either order.
                for window in keyed.windows(2) {
                    if window[0].0 == window[1].0 {
                        return Err(Error::custom("duplicate map key"));
                    }
                }

                entries.extend(keyed.into_iter().map(|(_, key, val)| (key, val)));
            }

            _ => {}
        }

        Ok(())
    }
}
