//! Version-paired data for the internal original named-arm qmatch component.
//! The shared carrier codec retains complete interfaces. These constructors
//! and readers confer no semantic acceptance, execution handle or capability.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0

use super::carrier::{Atom, Interface};
use super::json::{self, Value};
use super::{Error, Result};

/// Original physical arm subjects, still untrusted until the enclosing source
/// and carrier-sector check. A physical signature is not a nominal contract.
pub(crate) enum ArmBody {
    Evidence(std::sync::Arc<crate::contract::FunctionEvidence>),
    Physical {
        bits: u32,
        raw: crate::ir::RawProgram,
        identity: Box<crate::contract::function::RetainedIdentity>,
    },
}

pub(crate) struct ArmSubject {
    pub body: ArmBody,
    pub controlled: crate::ir::RawProgram,
}

/// Pack actual source/body subjects with the shared QIRF encoder. The returned
/// bytes are a proposal only; indices are derived from this exact graph.
pub(crate) fn proposal(
    raw: &crate::ir::RawProgram,
    interface: Interface,
    source: SourceSite,
    arms: &[ArmSubject],
    sources: &[(String, String)],
) -> Result<(Vec<u8>, Vec<u8>)> {
    if arms.is_empty() || arms.len() > 64 {
        return Err(Error::limit("qmatch arm capacity"));
    }
    let mut remaining = json::MAX_BYTES;
    interface_storage(&interface, &mut remaining)?;
    let mut encoder = super::Encoder::new(super::Version::V2);
    for (name, text) in sources {
        encoder.source(name, text)?;
    }
    let (root, mut encoder) = super::prepare_proposal(raw, None, encoder)?;
    let mut indices = Vec::with_capacity(arms.len());
    for arm in arms {
        let evidence = match &arm.body {
            ArmBody::Evidence(evidence) => encoder.evidence(evidence)?,
            ArmBody::Physical {
                bits,
                raw,
                identity,
            } => {
                // Encode a proposal, not a FunctionEvidence constructor. The
                // fresh source gate associates this entry with the original
                // full target type and checks both actual encoded bodies.
                encoder.object()?;
                let index = encoder.entries.len();
                encoder.entries.push(Value::Null);
                encoder.evidence_fields(
                    index,
                    &crate::contract::BasisType::Bits(*bits),
                    raw,
                    raw,
                    identity.parts(),
                    None,
                )?;
                index
            }
        };
        indices.push(Arm {
            evidence: evidence as u32,
            controlled: encoder.program(&arm.controlled)? as u32,
        });
    }
    let request = Request {
        required: interface.clone(),
        attached: interface,
        source,
        arms: indices,
    };
    Ok((
        super::finish_proposal(root, None, encoder)?,
        request.encode()?,
    ))
}

const PROFILE: &str = "finite-source-qmatch-named-v1";

/// An actual original UTF-8 byte occurrence, independently read by Lean.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceSite {
    pub module: String,
    pub function: String,
    pub offset: u32,
}

/// Evidence names an original QIRF entry, rather than a free implementation.
/// The controlled program remains a separate checked subject.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Arm {
    pub evidence: u32,
    pub controlled: u32,
}

/// Untrusted request data. Labels, source types, logical matrices, graph roots
/// and success receipts cannot be supplied in place of independent checking.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Request {
    pub attached: Interface,
    pub required: Interface,
    pub source: SourceSite,
    pub arms: Vec<Arm>,
}

fn text(value: impl Into<String>) -> Value {
    Value::String(value.into())
}

fn n(value: u32) -> Value {
    Value::Number(u64::from(value))
}

fn number(value: &Value) -> Result<u32> {
    u32::try_from(value.number()?).map_err(|_| Error::format("qmatch index exceeds u32"))
}

fn charge(remaining: &mut usize, amount: usize) -> Result<()> {
    *remaining = remaining
        .checked_sub(amount)
        .ok_or_else(|| Error::limit("qmatch request allocation capacity"))?;
    Ok(())
}

// Bound all interface string/object copies before constructing a JSON tree.
// This is allocation accounting, not finite type or code-space acceptance.
fn interface_storage(value: &Interface, remaining: &mut usize) -> Result<()> {
    for owners in [&value.inputs, &value.outputs] {
        if owners.len() > 128 {
            return Err(Error::limit("carrier owner capacity"));
        }
        for owner in owners {
            if owner.basis.len() > 128 {
                return Err(Error::limit("carrier node capacity"));
            }
            charge(
                remaining,
                128usize.saturating_add(owner.port.wires.len().saturating_mul(24)),
            )?;
            for atom in &owner.basis {
                charge(remaining, 64)?;
                if let Atom::Enum(origin, names) | Atom::Record(origin, names) = atom {
                    for value in [&origin.module, &origin.declaration, &origin.source] {
                        charge(remaining, value.len().saturating_mul(6).saturating_add(32))?;
                    }
                    for name in names {
                        charge(remaining, name.len().saturating_mul(6).saturating_add(32))?;
                    }
                }
            }
        }
    }
    Ok(())
}

impl SourceSite {
    fn bounded(&self) -> Result<()> {
        if self.module.is_empty()
            || self.function.is_empty()
            || self.module.len() > 4096
            || self.function.len() > 4096
        {
            return Err(Error::format("qmatch source name capacity"));
        }
        Ok(())
    }

    fn encode(&self) -> Value {
        Value::object([
            ("module", text(&self.module)),
            ("function", text(&self.function)),
            ("offset", n(self.offset)),
        ])
    }

    fn decode(value: &Value) -> Result<Self> {
        value.fields(&["module", "function", "offset"])?;
        let source = Self {
            module: value.field("module")?.text()?.into(),
            function: value.field("function")?.text()?.into(),
            offset: number(value.field("offset")?)?,
        };
        source.bounded()?;
        Ok(source)
    }
}

impl Arm {
    fn encode(&self) -> Value {
        Value::object([
            ("evidence", n(self.evidence)),
            ("controlled", n(self.controlled)),
        ])
    }

    fn decode(value: &Value) -> Result<Self> {
        value.fields(&["evidence", "controlled"])?;
        Ok(Self {
            evidence: number(value.field("evidence")?)?,
            controlled: number(value.field("controlled")?)?,
        })
    }
}

impl Request {
    /// Encode bounded data only; no native dispatch or acceptance follows.
    pub fn encode(&self) -> Result<Vec<u8>> {
        self.source.bounded()?;
        if self.arms.is_empty() || self.arms.len() > 64 {
            return Err(Error::limit("qmatch arm capacity"));
        }
        let mut remaining = json::MAX_BYTES;
        interface_storage(&self.attached, &mut remaining)?;
        interface_storage(&self.required, &mut remaining)?;
        charge(
            &mut remaining,
            (self.source.module.len() + self.source.function.len())
                .saturating_mul(6)
                .saturating_add(self.arms.len().saturating_mul(128))
                .saturating_add(512),
        )?;
        json::encode(&Value::object([
            ("format", text("qleisli.qmatch-request")),
            ("version", n(1)),
            ("profile", text(PROFILE)),
            ("attached", self.attached.encode()),
            ("required", self.required.encode()),
            ("source", self.source.encode()),
            (
                "arms",
                Value::Array(self.arms.iter().map(Arm::encode).collect()),
            ),
        ]))
    }

    /// Decode retained data, without issuing a handle or trusting source names.
    pub fn decode(bytes: &[u8]) -> Result<Self> {
        let value = json::parse(bytes)?;
        value.fields(&[
            "format", "version", "profile", "attached", "required", "source", "arms",
        ])?;
        if value.field("format")?.text()? != "qleisli.qmatch-request"
            || value.field("version")?.number()? != 1
            || value.field("profile")?.text()? != PROFILE
        {
            return Err(Error::format("unsupported qmatch request profile"));
        }
        let arms = value.field("arms")?.array()?;
        if arms.is_empty() || arms.len() > 64 {
            return Err(Error::limit("qmatch arm capacity"));
        }
        Ok(Self {
            attached: Interface::decode(value.field("attached")?)?,
            required: Interface::decode(value.field("required")?)?,
            source: SourceSite::decode(value.field("source")?)?,
            arms: arms.iter().map(Arm::decode).collect::<Result<_>>()?,
        })
    }
}

#[cfg(test)]
mod tests;
