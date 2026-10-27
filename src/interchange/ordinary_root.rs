//! Internal closed ordinary-result metadata. Construction grants no acceptance.
//! Lean reads the original declaration, actual output map and every history.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use std::sync::Arc;

use super::carrier::{Atom, Origin};
use super::json::{self, Value};
use super::{Error, Result};
use crate::ir::{ClassicalId, Effect};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Selection {
    Project,
    Exported,
}

impl Selection {
    pub(super) fn name(self) -> &'static str {
        match self {
            Self::Project => "project",
            Self::Exported => "exported",
        }
    }
}

/// Complete typed output tree over actual classical SSA identities. Zero-width
/// nodes and nominal/field order remain explicit rather than erased to bits.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Storage {
    Unit,
    Bit(ClassicalId),
    Bits(Vec<ClassicalId>),
    Pair(Box<Storage>, Box<Storage>),
    Tuple(Vec<Storage>),
    Enum(Arc<Origin>, Vec<ClassicalId>),
    Record(Arc<Origin>, Vec<(String, Storage)>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Request {
    pub selection: Selection,
    pub module: String,
    pub declaration: String,
    pub basis: Vec<Atom>,
    pub storage: Storage,
    pub public_effect: Effect,
}

fn text(value: impl Into<String>) -> Value {
    Value::String(value.into())
}
fn ids(values: &[ClassicalId]) -> Value {
    Value::Array(
        values
            .iter()
            .map(|id| Value::Number(u64::from(id.0)))
            .collect(),
    )
}
fn read_id(value: &Value) -> Result<ClassicalId> {
    Ok(ClassicalId(u32::try_from(value.number()?).map_err(
        |_| Error::format("ordinary index exceeds u32"),
    )?))
}
fn read_ids(value: &Value) -> Result<Vec<ClassicalId>> {
    let values = value.array()?;
    if values.len() > 6 {
        return Err(Error::limit("ordinary storage width exceeds six bits"));
    }
    values.iter().map(read_id).collect()
}

impl Storage {
    fn encode(&self) -> Value {
        let (tag, fields) = match self {
            Self::Unit => ("unit", vec![]),
            Self::Bit(id) => ("bit", vec![("id", Value::Number(u64::from(id.0)))]),
            Self::Bits(values) => ("bits", vec![("ids", ids(values))]),
            Self::Pair(first, second) => (
                "pair",
                vec![("first", first.encode()), ("second", second.encode())],
            ),
            Self::Tuple(fields) => (
                "tuple",
                vec![(
                    "fields",
                    Value::Array(fields.iter().map(Self::encode).collect()),
                )],
            ),
            Self::Enum(origin, values) => (
                "enum",
                vec![("origin", origin.encode()), ("ids", ids(values))],
            ),
            Self::Record(origin, fields) => (
                "record",
                vec![
                    ("origin", origin.encode()),
                    (
                        "fields",
                        Value::Array(
                            fields
                                .iter()
                                .map(|(name, value)| {
                                    Value::object([("name", text(name)), ("value", value.encode())])
                                })
                                .collect(),
                        ),
                    ),
                ],
            ),
        };
        Value::object(std::iter::once(("tag", text(tag))).chain(fields))
    }

    fn decode(value: &Value, depth: usize, remaining: &mut usize) -> Result<Self> {
        if depth > 32 || *remaining == 0 {
            return Err(Error::limit(
                "ordinary storage exceeds 128 nodes or depth 32",
            ));
        }
        *remaining -= 1;
        Ok(match value.field("tag")?.text()? {
            "unit" => {
                value.fields(&["tag"])?;
                Self::Unit
            }
            "bit" => {
                value.fields(&["tag", "id"])?;
                Self::Bit(read_id(value.field("id")?)?)
            }
            "bits" => {
                value.fields(&["tag", "ids"])?;
                Self::Bits(read_ids(value.field("ids")?)?)
            }
            "pair" => {
                value.fields(&["tag", "first", "second"])?;
                Self::Pair(
                    Box::new(Self::decode(value.field("first")?, depth + 1, remaining)?),
                    Box::new(Self::decode(value.field("second")?, depth + 1, remaining)?),
                )
            }
            "tuple" => {
                value.fields(&["tag", "fields"])?;
                Self::Tuple(
                    value
                        .field("fields")?
                        .array()?
                        .iter()
                        .map(|field| Self::decode(field, depth + 1, remaining))
                        .collect::<Result<_>>()?,
                )
            }
            "enum" => {
                value.fields(&["tag", "origin", "ids"])?;
                Self::Enum(
                    Arc::new(Origin::decode(value.field("origin")?)?),
                    read_ids(value.field("ids")?)?,
                )
            }
            "record" => {
                value.fields(&["tag", "origin", "fields"])?;
                let origin = Arc::new(Origin::decode(value.field("origin")?)?);
                let fields = value
                    .field("fields")?
                    .array()?
                    .iter()
                    .map(|field| {
                        field.fields(&["name", "value"])?;
                        Ok((
                            field.field("name")?.text()?.to_owned(),
                            Self::decode(field.field("value")?, depth + 1, remaining)?,
                        ))
                    })
                    .collect::<Result<_>>()?;
                Self::Record(origin, fields)
            }
            _ => return Err(Error::format("unknown ordinary storage tag")),
        })
    }
}

impl Request {
    pub fn encode(&self) -> Result<Vec<u8>> {
        // Check bounded data before recursive copying and serialization.
        self.preflight()?;
        json::encode(&Value::object([
            ("format", text("qleisli.ordinary-root-request")),
            ("version", Value::Number(1)),
            ("profile", text("finite-ordinary-root-v1")),
            ("selection", text(self.selection.name())),
            ("module", text(&self.module)),
            ("declaration", text(&self.declaration)),
            (
                "basis",
                Value::Array(self.basis.iter().map(Atom::encode).collect()),
            ),
            ("storage", self.storage.encode()),
            (
                "public_effect",
                text(match self.public_effect {
                    Effect::Unitary => "unitary",
                    Effect::Isometry => "isometry",
                    Effect::Observe => "observe",
                }),
            ),
        ]))
    }

    fn preflight(&self) -> Result<()> {
        if self.basis.len() > 128 {
            return Err(Error::limit("ordinary basis node capacity"));
        }
        let mut pending = vec![(&self.storage, 0usize)];
        let (mut nodes, mut bits) = (0usize, 0usize);
        while let Some((value, depth)) = pending.pop() {
            nodes += 1;
            if nodes > 128 || depth > 32 {
                return Err(Error::limit(
                    "ordinary storage exceeds 128 nodes or depth 32",
                ));
            }
            match value {
                Storage::Unit => {}
                Storage::Bit(_) => bits += 1,
                Storage::Bits(ids) | Storage::Enum(_, ids) => bits += ids.len(),
                Storage::Pair(a, b) => {
                    pending.extend([(b.as_ref(), depth + 1), (a.as_ref(), depth + 1)])
                }
                Storage::Tuple(fields) => {
                    pending.extend(fields.iter().rev().map(|v| (v, depth + 1)))
                }
                Storage::Record(_, fields) => {
                    pending.extend(fields.iter().rev().map(|(_, v)| (v, depth + 1)))
                }
            }
            if pending.len() > 128 || bits > 6 {
                return Err(Error::limit("ordinary storage capacity"));
            }
        }
        Ok(())
    }

    pub fn decode(bytes: &[u8]) -> Result<Self> {
        let value = json::parse(bytes)?;
        value.fields(&[
            "format",
            "version",
            "profile",
            "selection",
            "module",
            "declaration",
            "basis",
            "storage",
            "public_effect",
        ])?;
        if value.field("format")?.text()? != "qleisli.ordinary-root-request"
            || value.field("version")?.number()? != 1
            || value.field("profile")?.text()? != "finite-ordinary-root-v1"
        {
            return Err(Error::format("unsupported ordinary root request"));
        }
        let atoms = value.field("basis")?.array()?;
        if atoms.len() > 128 {
            return Err(Error::limit("ordinary basis node capacity"));
        }
        let result = Self {
            selection: match value.field("selection")?.text()? {
                "project" => Selection::Project,
                "exported" => Selection::Exported,
                _ => return Err(Error::format("unknown ordinary entry selection")),
            },
            module: value.field("module")?.text()?.into(),
            declaration: value.field("declaration")?.text()?.into(),
            basis: atoms.iter().map(Atom::decode).collect::<Result<_>>()?,
            storage: Storage::decode(value.field("storage")?, 0, &mut 128)?,
            public_effect: match value.field("public_effect")?.text()? {
                "unitary" => Effect::Unitary,
                "isometry" => Effect::Isometry,
                "observe" => Effect::Observe,
                _ => return Err(Error::format("unknown ordinary public effect")),
            },
        };
        result.preflight()?;
        Ok(result)
    }
}
