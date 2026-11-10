//! Version-paired data for original primitive and named-arm qmatch contexts.
//! The shared carrier codec retains complete interfaces. These constructors
//! and readers confer no semantic acceptance, execution handle or capability.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0

use super::carrier::{Atom, Interface};
use super::json::{self, Value};
use super::{Error, Result};

mod context;
pub use context::{BodyRequest, Branch, Call, Context, ContextArm, ContextSite, ProviderSubject};
mod operations;
pub use operations::{Description, OperationNode, OperationPrimitive, StaticArguments};
pub mod v5;

/// Original physical arm subjects, still untrusted until the enclosing source
/// and carrier-sector check. A physical signature is not a nominal contract.
pub(crate) enum ArmBody {
    Evidence(std::sync::Arc<crate::contract::FunctionEvidence>),
    /// The standalone forward circuit of an original primitive or operation tree.
    /// The complete source request separately checks each original provider.
    #[cfg_attr(
        not(test),
        allow(
            dead_code,
            reason = "retained v5 source subjects pending production composition"
        )
    )]
    Program(crate::ir::RawProgram),
    Physical {
        bits: u32,
        raw: crate::ir::RawProgram,
        identity: Box<crate::contract::function::RetainedIdentity>,
    },
}

#[cfg_attr(
    not(test),
    allow(
        dead_code,
        reason = "retained v5 source subjects pending production composition"
    )
)]
pub(crate) struct ArmSubject {
    pub body: ArmBody,
    pub controlled: crate::ir::RawProgram,
    pub operation: Option<std::sync::Arc<OperationSubject>>,
}

/// Retained original provider subjects in descriptor child-edge postorder.
/// These objects remain proposals; Meaning reference bodies and demanded path
/// equations are derived independently before any v5 execution authority.
#[cfg_attr(
    not(test),
    allow(
        dead_code,
        reason = "retained v5 source subjects pending production composition"
    )
)]
pub(crate) enum OriginalBody {
    Function {
        evidence: std::sync::Arc<crate::contract::FunctionEvidence>,
        context: std::sync::Arc<ContextSubject>,
    },
    Pure {
        program: crate::AcceptedProgram,
        context: std::sync::Arc<ContextSubject>,
    },
}

#[cfg_attr(
    not(test),
    allow(
        dead_code,
        reason = "retained v5 source subjects pending production composition"
    )
)]
impl OriginalBody {
    pub(crate) fn context(&self) -> &std::sync::Arc<ContextSubject> {
        match self {
            Self::Function { context, .. } | Self::Pure { context, .. } => context,
        }
    }
}

#[cfg_attr(
    not(test),
    allow(
        dead_code,
        reason = "retained v5 source subjects pending production composition"
    )
)]
pub(crate) struct OperationSubject {
    pub description: Description,
    pub bodies: Vec<OriginalBody>,
    /// One group per original Meaning obligation, containing the actual quantum
    /// reference bodies in source order. Classical leaves need no program slot.
    pub meaning_references: Vec<Vec<OriginalBody>>,
}

/// Original lowering coordinates retained alongside the exact prepared body.
/// Encoding derives all graph indices afresh from these actual arm subjects.
#[derive(Default)]
#[cfg_attr(
    not(test),
    allow(
        dead_code,
        reason = "retained v5 source subjects pending production composition"
    )
)]
pub(crate) struct ContextSubject {
    pub supplies: Vec<(String, OperationSubject)>,
    pub positions: Vec<Position>,
    pub selections: Vec<SelectionBody>,
    pub calls: Vec<(Position, std::sync::Arc<ContextSubject>)>,
    pub branches: Vec<(
        Position,
        std::sync::Arc<ContextSubject>,
        std::sync::Arc<ContextSubject>,
    )>,
    /// An actual operation application has provider bodies and no fabricated
    /// containing-function prefix or nested runtime instruction coordinates.
    pub operation: Option<std::sync::Arc<OperationSubject>>,
    // Producer eligibility only; never serialized or trusted by a native gate.
    pub contains_selections: bool,
    pub requires_source_gate: bool,
    pub contains_unsupported_v5_event: bool,
    pub needs_qmatch_v5: bool,
}

#[cfg_attr(
    not(test),
    allow(
        dead_code,
        reason = "retained v5 source subjects pending production composition"
    )
)]
pub(crate) struct SelectionBody {
    pub interface: Interface,
    pub position: Position,
    pub arms: Vec<ArmSubject>,
}

impl std::fmt::Debug for ContextSubject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ContextSubject")
            .field("positions", &self.positions)
            .field("selections", &self.selections.len())
            .field("calls", &self.calls.len())
            .field("branches", &self.branches.len())
            .finish()
    }
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
    positions: &[Position],
    selections: &[SelectionSubject<'_>],
    sources: &[(String, String)],
) -> Result<(Vec<u8>, Vec<u8>)> {
    source.bounded()?;
    if selections.is_empty() || selections.len() > 128 {
        return Err(Error::limit("qmatch sequence capacity"));
    }
    let mut remaining = json::MAX_BYTES;
    positions_storage(positions.len(), &mut remaining)?;
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
                ArmBody::Program(_) => {
                    return Err(Error::new(
                        "unsupported",
                        "standalone qmatch arm programs require the complete v5 source gate. Wrap the gate in a named unitary function",
                    ));
                }
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
    let request = Request {
        source,
        positions: positions.to_vec(),
        sites,
    };
    Ok((
        super::finish_proposal(root, None, encoder)?,
        request.encode()?,
    ))
}

pub(crate) const PROFILE: &str = "finite-source-qmatch-context-v4";

/// The original containing function, independently read by Lean.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceSite {
    pub module: String,
    pub function: String,
}

/// Original callee-token or qmatch-keyword byte and literal Raw interval.
/// Positions retain evaluation order and supply no acceptance authority.
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
    /// Every original primitive/qmatch event, in actual evaluation order.
    pub positions: Vec<Position>,
    /// Arm requests belong only to qmatch selections.
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

fn positions_storage(count: usize, remaining: &mut usize) -> Result<()> {
    charge(remaining, count.saturating_mul(128).saturating_add(32))
}

// Bound all interface string/object copies before constructing a JSON tree.
// This is allocation accounting, not finite type or code-space acceptance.
fn interface_storage(value: &Interface, remaining: &mut usize) -> Result<()> {
    for owners in [&value.inputs, &value.outputs] {
        if owners.len() > 128 {
            return Err(Error::limit("carrier owner capacity"));
        }
        for owner in owners {
            charge(
                remaining,
                128usize.saturating_add(owner.port.wires.len().saturating_mul(24)),
            )?;
            basis_storage(&owner.basis, remaining)?;
        }
    }
    Ok(())
}

fn basis_storage(basis: &[Atom], remaining: &mut usize) -> Result<()> {
    if basis.len() > 128 {
        return Err(Error::limit("carrier node capacity"));
    }
    for atom in basis {
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

impl Position {
    fn encode(&self) -> Value {
        Value::object([
            ("offset", n(self.offset)),
            ("start", n(self.start)),
            ("count", n(self.count)),
        ])
    }

    fn decode(value: &Value) -> Result<Self> {
        value.fields(&["offset", "start", "count"])?;
        Ok(Self {
            offset: number(value.field("offset")?)?,
            start: number(value.field("start")?)?,
            count: number(value.field("count")?)?,
        })
    }
}

impl Request {
    fn bounded(&self) -> Result<()> {
        self.source.bounded()?;
        if self.sites.is_empty() || self.sites.len() > 128 {
            return Err(Error::limit("qmatch sequence capacity"));
        }
        let mut remaining = json::MAX_BYTES;
        positions_storage(self.positions.len(), &mut remaining)?;
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
        )
    }

    /// Encode bounded data only; no native dispatch or acceptance follows.
    pub fn encode(&self) -> Result<Vec<u8>> {
        self.bounded()?;
        json::encode(&Value::object([
            ("format", text("qleisli.qmatch-request")),
            ("version", n(4)),
            ("profile", text(PROFILE)),
            ("source", self.source.encode()),
            (
                "positions",
                Value::Array(self.positions.iter().map(Position::encode).collect()),
            ),
            (
                "sites",
                Value::Array(self.sites.iter().map(Site::encode).collect()),
            ),
        ]))
    }

    /// Decode retained data, without issuing a handle or trusting source names.
    pub fn decode(bytes: &[u8]) -> Result<Self> {
        let value = json::parse(bytes)?;
        value.fields(&[
            "format",
            "version",
            "profile",
            "source",
            "positions",
            "sites",
        ])?;
        if value.field("format")?.text()? != "qleisli.qmatch-request"
            || value.field("version")?.number()? != 4
            || value.field("profile")?.text()? != PROFILE
        {
            return Err(Error::format("unsupported qmatch request profile"));
        }
        let sites = value.field("sites")?.array()?;
        if sites.is_empty() || sites.len() > 128 {
            return Err(Error::limit("qmatch sequence capacity"));
        }
        let positions = value.field("positions")?.array()?;
        // Reserve the full event vector before copying it; its bound is the
        // existing packet allocation budget, not the qmatch selection count.
        let mut remaining = json::MAX_BYTES;
        positions_storage(positions.len(), &mut remaining)?;
        let request = Self {
            source: SourceSite::decode(value.field("source")?)?,
            positions: positions
                .iter()
                .map(Position::decode)
                .collect::<Result<_>>()?,
            sites: sites.iter().map(Site::decode).collect::<Result<_>>()?,
        };
        request.bounded()?;
        Ok(request)
    }
}

impl Site {
    fn encode(&self) -> Value {
        Value::object([
            ("attached", self.attached.encode()),
            ("required", self.required.encode()),
            ("position", self.position.encode()),
            (
                "arms",
                Value::Array(self.arms.iter().map(Arm::encode).collect()),
            ),
        ])
    }

    fn decode(value: &Value) -> Result<Self> {
        value.fields(&["attached", "required", "position", "arms"])?;
        let arms = value.field("arms")?.array()?;
        if arms.is_empty() || arms.len() > 64 {
            return Err(Error::limit("qmatch arm capacity"));
        }
        Ok(Self {
            attached: Interface::decode(value.field("attached")?)?,
            required: Interface::decode(value.field("required")?)?,
            position: Position::decode(value.field("position")?)?,
            arms: arms.iter().map(Arm::decode).collect::<Result<_>>()?,
        })
    }
}

#[cfg(test)]
mod tests;
