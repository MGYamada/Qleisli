//! Internal version-1 finite-carrier request data. These descriptions grant no
//! acceptance, source preservation, inverse or controlled access. The native
//! pure profile reconstructs original declarations and checks the actual body.
//! Ordinary source ADT construction/matching is a separate unfinished frontend.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0

use std::sync::Arc;

use super::json::{self, Value};
use super::{Error, Result, finite_matrix};
use crate::contract::DEFAULT_EXACT_WORK;
use crate::contract::exact::{Budget, Matrix};
use crate::ir::{BasisShape, Effect, QuantumPort, TokenId, WireId};

/// Complete original nominal identity, independently looked up by Lean.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Origin {
    pub module: String,
    pub declaration: String,
    pub source: String,
}

/// Flat prefix transport, retaining logical identity independently of width.
/// Record children follow their declared field order. No owner split is implied.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Atom {
    Unit,
    Bit,
    Bits(u32),
    Pair,
    Tuple(u32),
    Enum(Arc<Origin>, Vec<String>),
    Record(Arc<Origin>, Vec<String>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Owner {
    pub port: QuantumPort,
    pub basis: Vec<Atom>,
}

/// Ordered owners include singleton and zero-width types; effect is public data.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Interface {
    pub inputs: Vec<Owner>,
    pub outputs: Vec<Owner>,
    pub public_effect: Effect,
}

/// Untrusted attached types and independently required exact logical action.
/// Data construction/decoding is not an equation or isometry judgment.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Request {
    pub attached: Interface,
    pub required: Interface,
    pub logical: Matrix,
}

fn text(value: impl Into<String>) -> Value {
    Value::String(value.into())
}
fn n(value: u32) -> Value {
    Value::Number(u64::from(value))
}
fn number(value: &Value) -> Result<u32> {
    u32::try_from(value.number()?).map_err(|_| Error::format("carrier index exceeds u32"))
}

impl Origin {
    fn encode(&self) -> Value {
        Value::object([
            ("module", text(&self.module)),
            ("declaration", text(&self.declaration)),
            ("source", text(&self.source)),
        ])
    }

    fn decode(value: &Value) -> Result<Self> {
        value.fields(&["module", "declaration", "source"])?;
        Ok(Self {
            module: value.field("module")?.text()?.into(),
            declaration: value.field("declaration")?.text()?.into(),
            source: value.field("source")?.text()?.into(),
        })
    }
}

impl Atom {
    fn encode(&self) -> Value {
        let (tag, fields) = match self {
            Self::Unit => ("unit", vec![]),
            Self::Bit => ("bit", vec![]),
            Self::Bits(width) => ("bits", vec![("width", n(*width))]),
            Self::Pair => ("pair", vec![]),
            Self::Tuple(arity) => ("tuple", vec![("arity", n(*arity))]),
            Self::Enum(origin, members) | Self::Record(origin, members) => (
                if matches!(self, Self::Enum(..)) {
                    "enum"
                } else {
                    "record"
                },
                vec![
                    ("origin", origin.encode()),
                    ("members", Value::Array(members.iter().map(text).collect())),
                ],
            ),
        };
        Value::object(std::iter::once(("tag", text(tag))).chain(fields))
    }

    fn decode(value: &Value) -> Result<Self> {
        Ok(match value.field("tag")?.text()? {
            "unit" => {
                value.fields(&["tag"])?;
                Self::Unit
            }
            "bit" => {
                value.fields(&["tag"])?;
                Self::Bit
            }
            "bits" => {
                value.fields(&["tag", "width"])?;
                Self::Bits(number(value.field("width")?)?)
            }
            "pair" => {
                value.fields(&["tag"])?;
                Self::Pair
            }
            "tuple" => {
                value.fields(&["tag", "arity"])?;
                Self::Tuple(number(value.field("arity")?)?)
            }
            tag @ ("enum" | "record") => {
                value.fields(&["tag", "origin", "members"])?;
                let origin = Arc::new(Origin::decode(value.field("origin")?)?);
                let members = value
                    .field("members")?
                    .array()?
                    .iter()
                    .map(|member| Ok(member.text()?.to_owned()))
                    .collect::<Result<_>>()?;
                if tag == "enum" {
                    Self::Enum(origin, members)
                } else {
                    Self::Record(origin, members)
                }
            }
            _ => return Err(Error::format("unknown carrier atom")),
        })
    }
}

impl Owner {
    fn encode(&self) -> Value {
        Value::object([
            (
                "port",
                Value::object([
                    ("token", n(self.port.token.0)),
                    (
                        "wires",
                        Value::Array(self.port.wires.iter().map(|wire| n(wire.0)).collect()),
                    ),
                    ("bits", n(u32::from(self.port.shape.bits))),
                ]),
            ),
            (
                "basis",
                Value::Array(self.basis.iter().map(Atom::encode).collect()),
            ),
        ])
    }

    fn decode(value: &Value) -> Result<Self> {
        value.fields(&["port", "basis"])?;
        let port = value.field("port")?;
        port.fields(&["token", "wires", "bits"])?;
        let atoms = value.field("basis")?.array()?;
        if atoms.len() > 128 {
            return Err(Error::limit("carrier node capacity"));
        }
        Ok(Self {
            port: QuantumPort {
                token: TokenId(number(port.field("token")?)?),
                wires: port
                    .field("wires")?
                    .array()?
                    .iter()
                    .map(|n| Ok(WireId(number(n)?)))
                    .collect::<Result<_>>()?,
                shape: BasisShape {
                    bits: u8::try_from(number(port.field("bits")?)?)
                        .map_err(|_| Error::format("carrier port bits exceed u8"))?,
                },
            },
            basis: atoms.iter().map(Atom::decode).collect::<Result<_>>()?,
        })
    }
}

impl Interface {
    fn encode(&self) -> Value {
        Value::object([
            (
                "inputs",
                Value::Array(self.inputs.iter().map(Owner::encode).collect()),
            ),
            (
                "outputs",
                Value::Array(self.outputs.iter().map(Owner::encode).collect()),
            ),
            (
                "public_effect",
                text(match self.public_effect {
                    Effect::Unitary => "unitary",
                    Effect::Isometry => "isometry",
                    Effect::Observe => "observe",
                }),
            ),
        ])
    }

    fn decode(value: &Value) -> Result<Self> {
        value.fields(&["inputs", "outputs", "public_effect"])?;
        let owners = |name| -> Result<Vec<Owner>> {
            let values = value.field(name)?.array()?;
            if values.len() > 128 {
                return Err(Error::limit("carrier owner capacity"));
            }
            values.iter().map(Owner::decode).collect()
        };
        Ok(Self {
            inputs: owners("inputs")?,
            outputs: owners("outputs")?,
            public_effect: match value.field("public_effect")?.text()? {
                "unitary" => Effect::Unitary,
                "isometry" => Effect::Isometry,
                "observe" => Effect::Observe,
                _ => return Err(Error::format("unknown public carrier effect")),
            },
        })
    }
}

impl Request {
    /// Encode data only; semantic checks belong to the fresh native invocation.
    pub fn encode(&self) -> Result<Vec<u8>> {
        json::encode(&Value::object([
            ("format", text("qleisli.carrier-request")),
            ("version", n(1)),
            ("profile", text("finite-carrier-pure-v1")),
            ("attached", self.attached.encode()),
            ("required", self.required.encode()),
            (
                "logical",
                json::parse(&finite_matrix::encode(&self.logical)?)?,
            ),
        ]))
    }

    /// Decode retained data only. This cannot construct an accepted handle.
    pub fn decode(bytes: &[u8]) -> Result<Self> {
        let value = json::parse(bytes)?;
        value.fields(&[
            "format", "version", "profile", "attached", "required", "logical",
        ])?;
        if value.field("format")?.text()? != "qleisli.carrier-request"
            || value.field("version")?.number()? != 1
            || value.field("profile")?.text()? != "finite-carrier-pure-v1"
        {
            return Err(Error::format("unsupported finite carrier request profile"));
        }
        let mut budget = Budget::new(DEFAULT_EXACT_WORK);
        Ok(Self {
            attached: Interface::decode(value.field("attached")?)?,
            required: Interface::decode(value.field("required")?)?,
            logical: finite_matrix::decode(&json::encode(value.field("logical")?)?, &mut budget)?,
        })
    }
}
