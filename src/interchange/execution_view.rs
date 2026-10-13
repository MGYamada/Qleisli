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
