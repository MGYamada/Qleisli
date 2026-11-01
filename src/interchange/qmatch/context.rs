//! Literal requests retain each original call and arm-body occurrence.
//! Equal evidence indices never identify original static instantiations.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ContextSite {
    pub attached: Interface,
    pub required: Interface,
    pub position: Position,
    pub arms: Vec<ContextArm>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ContextArm {
    pub implementation: u32,
    pub controlled: u32,
    pub providers: Vec<ProviderSubject>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProviderSubject {
    Function { evidence: u32 },
    Pure { program: u32 },
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Context {
    pub positions: Vec<Position>,
    pub sites: Vec<ContextSite>,
    pub calls: Vec<Call>,
    pub bodies: Vec<Context>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Call {
    pub position: Position,
    pub body: Context,
}

impl Context {
    pub(super) fn bounded(&self, depth: usize, remaining: &mut usize) -> Result<()> {
        if depth > 128 || self.sites.len() > 128 {
            return Err(Error::limit("qmatch source context capacity"));
        }
        positions_storage(self.positions.len(), remaining)?;
        charge(remaining, self.calls.len().saturating_mul(160))?;
        charge(remaining, self.bodies.len().saturating_mul(64))?;
        for site in &self.sites {
            interface_storage(&site.attached, remaining)?;
            interface_storage(&site.required, remaining)?;
            if site.arms.is_empty() || site.arms.len() > 64 {
                return Err(Error::limit("qmatch arm capacity"));
            }
            charge(remaining, site.arms.len().saturating_mul(128).saturating_add(512))?;
            for arm in &site.arms {
                if arm.providers.len() > 4096 {
                    return Err(Error::limit("qmatch provider occurrence capacity"));
                }
                charge(remaining, arm.providers.len().saturating_mul(64))?;
            }
        }
        for call in &self.calls {
            call.body.bounded(depth + 1, remaining)?;
        }
        for body in &self.bodies {
            body.bounded(depth + 1, remaining)?;
        }
        Ok(())
    }

    pub(super) fn fields(&self) -> [(String, Value); 4] {
        [
            ("positions".into(), Value::Array(self.positions.iter().map(Position::encode).collect())),
            ("sites".into(), Value::Array(self.sites.iter().map(ContextSite::encode).collect())),
            ("calls".into(), Value::Array(self.calls.iter().map(Call::encode).collect())),
            ("bodies".into(), Value::Array(self.bodies.iter().map(Self::encode).collect())),
        ]
    }

    pub(super) fn encode(&self) -> Value {
        Value::object(self.fields())
    }

    pub(super) fn decode(value: &Value, depth: usize, remaining: &mut usize) -> Result<Self> {
        value.fields(&["positions", "sites", "calls", "bodies"])?;
        Self::decode_fields(value, depth, remaining)
    }

    pub(super) fn decode_fields(value: &Value, depth: usize, remaining: &mut usize) -> Result<Self> {
        if depth > 128 {
            return Err(Error::limit("qmatch source context depth"));
        }
        let positions = value.field("positions")?.array()?;
        let sites = value.field("sites")?.array()?;
        let calls = value.field("calls")?.array()?;
        let bodies = value.field("bodies")?.array()?;
        if sites.len() > 128 {
            return Err(Error::limit("qmatch sequence capacity"));
        }
        positions_storage(positions.len(), remaining)?;
        charge(remaining, sites.len().saturating_mul(512))?;
        charge(remaining, calls.len().saturating_mul(160))?;
        charge(remaining, bodies.len().saturating_mul(64))?;
        Ok(Self {
            positions: positions.iter().map(Position::decode).collect::<Result<_>>()?,
            sites: sites.iter().map(ContextSite::decode).collect::<Result<_>>()?,
            calls: calls.iter().map(|call| Call::decode(call, depth + 1, remaining)).collect::<Result<_>>()?,
            bodies: bodies.iter().map(|body| Self::decode(body, depth + 1, remaining)).collect::<Result<_>>()?,
        })
    }
}

impl ContextSite {
    fn encode(&self) -> Value {
        Value::object([
            ("attached", self.attached.encode()), ("required", self.required.encode()),
            ("position", self.position.encode()),
            ("arms", Value::Array(self.arms.iter().map(ContextArm::encode).collect())),
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
            arms: arms.iter().map(ContextArm::decode).collect::<Result<_>>()?,
        })
    }
}

impl ContextArm {
    fn encode(&self) -> Value {
        Value::object([
            ("implementation", n(self.implementation)), ("controlled", n(self.controlled)),
            ("providers", Value::Array(self.providers.iter().map(ProviderSubject::encode).collect())),
        ])
    }
    fn decode(value: &Value) -> Result<Self> {
        value.fields(&["implementation", "controlled", "providers"])?;
        let providers = value.field("providers")?.array()?;
        if providers.len() > 4096 {
            return Err(Error::limit("qmatch provider occurrence capacity"));
        }
        Ok(Self {
            implementation: number(value.field("implementation")?)?, controlled: number(value.field("controlled")?)?,
            providers: providers.iter().map(ProviderSubject::decode).collect::<Result<_>>()?,
        })
    }
}

impl ProviderSubject {
    fn encode(&self) -> Value {
        match self {
            Self::Function { evidence } => Value::object([("kind", text("function")), ("evidence", n(*evidence))]),
            Self::Pure { program } => Value::object([("kind", text("pure")), ("program", n(*program))]),
        }
    }
    fn decode(value: &Value) -> Result<Self> {
        Ok(match value.field("kind")?.text()? {
            "function" => { value.fields(&["kind", "evidence"])?; Self::Function { evidence: number(value.field("evidence")?)? } }
            "pure" => { value.fields(&["kind", "program"])?; Self::Pure { program: number(value.field("program")?)? } }
            _ => return Err(Error::format("unknown qmatch provider subject")),
        })
    }
}

impl Call {
    fn encode(&self) -> Value {
        Value::object([("position", self.position.encode()), ("body", self.body.encode())])
    }

    fn decode(value: &Value, depth: usize, remaining: &mut usize) -> Result<Self> {
        value.fields(&["position", "body"])?;
        Ok(Self {
            position: Position::decode(value.field("position")?)?,
            body: Context::decode(value.field("body")?, depth, remaining)?,
        })
    }
}
