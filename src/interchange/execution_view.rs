//! Canonical byte encoding for execution-view descriptions (QDV1).
//! This transport encoder has no acceptance authority. Production walkers and
//! native comparison are required before it can bind an execution view.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0

use super::{Error, Result};

pub(super) const MAX_BYTES: usize = 64 << 20;
const MAX_DEPTH: usize = 128;

#[cfg(test)]
#[derive(Clone, Debug)]
pub(super) enum Value {
    Null,
    Bool(bool),
    Natural(u64),
    Text(String),
    Array(Vec<Self>),
}

struct Writer {
    bytes: Vec<u8>,
    limit: usize,
    depth: usize,
}

impl Writer {
    fn append(&mut self, bytes: &[u8]) -> Result<()> {
        if self.depth > MAX_DEPTH {
            return Err(Error::limit(
                "canonical execution view exceeds depth capacity",
            ));
        }
        if bytes.len() > self.limit.saturating_sub(self.bytes.len()) {
            return Err(Error::limit(
                "canonical execution view exceeds byte capacity",
            ));
        }
        self.bytes.extend_from_slice(bytes);
        Ok(())
    }

    fn sized(&mut self, tag: u8, length: usize) -> Result<()> {
        let length = u32::try_from(length)
            .map_err(|_| Error::limit("canonical execution view length exceeds u32"))?;
        self.append(&[tag])?;
        self.append(&length.to_le_bytes())
    }

    fn natural(&mut self, value: usize) -> Result<()> {
        let value = u64::try_from(value)
            .map_err(|_| Error::limit("canonical execution view natural exceeds u64"))?;
        self.append(&[3])?;
        self.append(&value.to_le_bytes())
    }

    fn text(&mut self, value: &str) -> Result<()> {
        self.sized(4, value.len())?;
        self.append(value.as_bytes())
    }

    #[cfg(test)]
    fn value(&mut self, value: &Value, depth: usize) -> Result<()> {
        if depth > MAX_DEPTH {
            return Err(Error::limit(
                "canonical execution view exceeds depth capacity",
            ));
        }
        match value {
            Value::Null => self.append(&[0]),
            Value::Bool(false) => self.append(&[1]),
            Value::Bool(true) => self.append(&[2]),
            Value::Natural(value) => {
                self.append(&[3])?;
                self.append(&value.to_le_bytes())
            }
            Value::Text(value) => {
                self.sized(4, value.len())?;
                self.append(value.as_bytes())
            }
            Value::Array(values) => {
                self.sized(5, values.len())?;
                for value in values {
                    self.value(value, depth + 1)?;
                }
                Ok(())
            }
        }
    }
}

/// Count the complete top-level QDV1 values in `bytes`, for debug checks of
/// declared record arities. `None` means the bytes are not a value sequence.
#[cfg(debug_assertions)]
fn top_level_values(bytes: &[u8]) -> Option<usize> {
    fn skip(bytes: &[u8], at: usize) -> Option<usize> {
        let length = |at: usize| -> Option<usize> {
            let raw: [u8; 4] = bytes.get(at + 1..at + 5)?.try_into().ok()?;
            usize::try_from(u32::from_le_bytes(raw)).ok()
        };
        match *bytes.get(at)? {
            0..=2 => Some(at + 1),
            3 => (at + 9 <= bytes.len()).then_some(at + 9),
            4 => {
                let end = at + 5 + length(at)?;
                (end <= bytes.len()).then_some(end)
            }
            5 => {
                let mut next = at + 5;
                for _ in 0..length(at)? {
                    next = skip(bytes, next)?;
                }
                Some(next)
            }
            _ => None,
        }
    }
    let (mut count, mut at) = (0, 0);
    while at < bytes.len() {
        at = skip(bytes, at)?;
        count += 1;
    }
    Some(count)
}

#[cfg(test)]
pub(super) fn encode(value: &Value) -> Result<Vec<u8>> {
    encode_with_limit(value, MAX_BYTES)
}

#[cfg(test)]
fn encode_with_limit(value: &Value, limit: usize) -> Result<Vec<u8>> {
    let mut writer = Writer {
        bytes: Vec::new(),
        limit,
        depth: 0,
    };
    writer.append(b"QDV1")?;
    writer.value(value, 0)?;
    Ok(writer.bytes)
}

pub(super) mod finite;

#[cfg(test)]
pub(super) mod tests {
    use super::*;
    use std::fmt::Write;

    pub(in crate::interchange) fn vector_value(value: &crate::interchange::json::Value) -> Value {
        use crate::interchange::json::Value as Json;
        match value {
            Json::Null => Value::Null,
            Json::Bool(v) => Value::Bool(*v),
            Json::Number(v) => Value::Natural(*v),
            Json::String(v) => Value::Text(v.clone()),
            Json::Array(v) => Value::Array(v.iter().map(vector_value).collect()),
            Json::Object(_) => panic!("canonical vectors cannot contain objects"),
        }
    }

    #[test]
    fn shared_vectors_preserve_types_order_unicode_and_unsigned_width() {
        let vectors = crate::interchange::json::parse(include_bytes!(
            "../../tests/fixtures/verification_v030/execution-view-binding/canonical-vectors.json"
        ))
        .unwrap();
        for row in vectors.array().unwrap() {
            let actual = encode(&vector_value(row.field("value").unwrap())).unwrap();
            let mut hex = String::new();
            for byte in actual {
                write!(&mut hex, "{byte:02x}").unwrap();
            }
            assert_eq!(
                hex,
                row.field("hex").unwrap().text().unwrap(),
                "{}",
                row.field("name").unwrap().text().unwrap()
            );
        }
    }

    #[cfg(debug_assertions)]
    #[test]
    fn record_arity_counter_walks_nested_values() {
        let encoded = encode(&Value::Array(vec![
            Value::Null,
            Value::Natural(7),
            Value::Text("ab".into()),
            Value::Array(vec![Value::Bool(true)]),
        ]))
        .unwrap();
        let body = &encoded[4..];
        assert_eq!(top_level_values(body), Some(1));
        // Skip the outer array header: its four elements remain.
        assert_eq!(top_level_values(&body[5..]), Some(4));
        assert_eq!(top_level_values(&body[..body.len() - 1]), None);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "QDV1 record `bad` declares 2 fields")]
    fn a_record_writing_fewer_fields_than_declared_fails_at_its_call_site() {
        let _ = finite::without_dependencies(|w| w.record("bad", 2, |w| w.n(1)));
    }

    #[test]
    fn incomplete_over_capacity_and_over_depth_values_never_return_bytes() {
        let value = Value::Text("𝄞".into());
        let encoded = encode(&value).unwrap();
        assert_eq!(encoded.len(), 13);
        assert_eq!(encode_with_limit(&value, 13).unwrap(), encoded);
        for limit in 0..13 {
            assert_eq!(encode_with_limit(&value, limit).unwrap_err().code, "limit");
        }
        let mut nested = Value::Null;
        for _ in 0..MAX_DEPTH {
            nested = Value::Array(vec![nested]);
        }
        assert!(encode(&nested).is_ok());
        nested = Value::Array(vec![nested]);
        assert_eq!(encode(&nested).unwrap_err().code, "limit");
    }
}
