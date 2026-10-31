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

/// Actual local interfaces and literal positions in the complete original call.
pub(crate) struct SelectionSubject<'a> {
    pub interface: &'a Interface,
    pub position: Position,
    pub arms: &'a [ArmSubject],
}

/// Pack actual source/body subjects with the shared QIRF encoder. The returned
/// bytes are a proposal only; indices are derived from this exact graph.
pub(crate) fn proposal(
    raw: &crate::ir::RawProgram,
    source: SourceSite,
    selections: &[SelectionSubject<'_>],
    sources: &[(String, String)],
) -> Result<(Vec<u8>, Vec<u8>)> {
    if selections.is_empty() || selections.len() > 128 {
        return Err(Error::limit("qmatch sequence capacity"));
    }
    let mut remaining = json::MAX_BYTES;
    for selection in selections {
        interface_storage(selection.interface, &mut remaining)?;
        interface_storage(selection.interface, &mut remaining)?;
        if selection.arms.is_empty() || selection.arms.len() > 64 {
            return Err(Error::limit("qmatch arm capacity"));
        }
    }
    let mut encoder = super::Encoder::new(super::Version::V2);
    for (name, text) in sources {
        encoder.source(name, text)?;
    }
    let (root, mut encoder) = super::prepare_proposal(raw, None, encoder)?;
    let mut sites = Vec::with_capacity(selections.len());
    for selection in selections {
        let mut indices = Vec::with_capacity(selection.arms.len());
        for arm in selection.arms {
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
        sites.push(Site {
            attached: selection.interface.clone(),
            required: selection.interface.clone(),
            position: selection.position.clone(),
            arms: indices,
        });
    }
    let request = Request { source, sites };
    Ok((
        super::finish_proposal(root, None, encoder)?,
        request.encode()?,
    ))
}

pub(crate) const PROFILE: &str = "finite-source-qmatch-named-v3";

/// The original containing function, independently read by Lean.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceSite {
    pub module: String,
    pub function: String,
}

/// Actual source occurrence and literal Raw interval; none supplies authority.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Position {
    pub offset: u32,
    pub start: u32,
    pub count: u32,
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
    pub source: SourceSite,
    pub sites: Vec<Site>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Site {
    pub attached: Interface,
    pub required: Interface,
    pub position: Position,
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
        ])
    }

    fn decode(value: &Value) -> Result<Self> {
        value.fields(&["module", "function"])?;
        let source = Self {
            module: value.field("module")?.text()?.into(),
            function: value.field("function")?.text()?.into(),
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
        if self.sites.is_empty() || self.sites.len() > 128 {
            return Err(Error::limit("qmatch sequence capacity"));
        }
        let mut remaining = json::MAX_BYTES;
        for site in &self.sites {
            interface_storage(&site.attached, &mut remaining)?;
            interface_storage(&site.required, &mut remaining)?;
            if site.arms.is_empty() || site.arms.len() > 64 {
                return Err(Error::limit("qmatch arm capacity"));
            }
            charge(
                &mut remaining,
                site.arms.len().saturating_mul(128).saturating_add(512),
            )?;
        }
        charge(
            &mut remaining,
            (self.source.module.len() + self.source.function.len())
                .saturating_mul(6)
                .saturating_add(512),
        )?;
        json::encode(&Value::object([
            ("format", text("qleisli.qmatch-request")),
            ("version", n(3)),
            ("profile", text(PROFILE)),
            ("source", self.source.encode()),
            (
                "sites",
                Value::Array(self.sites.iter().map(Site::encode).collect()),
            ),
        ]))
    }

    /// Decode retained data, without issuing a handle or trusting source names.
    pub fn decode(bytes: &[u8]) -> Result<Self> {
        let value = json::parse(bytes)?;
        value.fields(&["format", "version", "profile", "source", "sites"])?;
        if value.field("format")?.text()? != "qleisli.qmatch-request"
            || value.field("version")?.number()? != 3
            || value.field("profile")?.text()? != PROFILE
        {
            return Err(Error::format("unsupported qmatch request profile"));
        }
        let sites = value.field("sites")?.array()?;
        if sites.is_empty() || sites.len() > 128 {
            return Err(Error::limit("qmatch sequence capacity"));
        }
        Ok(Self {
            source: SourceSite::decode(value.field("source")?)?,
            sites: sites.iter().map(Site::decode).collect::<Result<_>>()?,
        })
    }
}

impl Site {
    fn encode(&self) -> Value {
        Value::object([
            ("attached", self.attached.encode()),
            ("required", self.required.encode()),
            (
                "position",
                Value::object([
                    ("offset", n(self.position.offset)),
                    ("start", n(self.position.start)),
                    ("count", n(self.position.count)),
                ]),
            ),
            (
                "arms",
                Value::Array(self.arms.iter().map(Arm::encode).collect()),
            ),
        ])
    }

    fn decode(value: &Value) -> Result<Self> {
        value.fields(&["attached", "required", "position", "arms"])?;
        let position = value.field("position")?;
        position.fields(&["offset", "start", "count"])?;
        let arms = value.field("arms")?.array()?;
        if arms.is_empty() || arms.len() > 64 {
            return Err(Error::limit("qmatch arm capacity"));
        }
        Ok(Self {
            attached: Interface::decode(value.field("attached")?)?,
            required: Interface::decode(value.field("required")?)?,
            position: Position {
                offset: number(position.field("offset")?)?,
                start: number(position.field("start")?)?,
                count: number(position.field("count")?)?,
            },
            arms: arms.iter().map(Arm::decode).collect::<Result<_>>()?,
        })
    }
}

#[cfg(test)]
mod tests;
