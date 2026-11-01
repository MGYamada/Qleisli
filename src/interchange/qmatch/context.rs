//! Literal requests retain each original call and arm-body occurrence.
//! Equal evidence indices never identify original static instantiations.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Context {
    pub positions: Vec<Position>,
    pub sites: Vec<Site>,
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
            ("sites".into(), Value::Array(self.sites.iter().map(Site::encode).collect())),
            ("calls".into(), Value::Array(self.calls.iter().map(Call::encode).collect())),
            ("bodies".into(), Value::Array(self.bodies.iter().map(Self::encode).collect())),
        ]
    }

    pub(super) fn encode(&self) -> Value {
        Value::Object(self.fields().into())
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
            sites: sites.iter().map(Site::decode).collect::<Result<_>>()?,
            calls: calls.iter().map(|call| Call::decode(call, depth + 1, remaining)).collect::<Result<_>>()?,
            bodies: bodies.iter().map(|body| Self::decode(body, depth + 1, remaining)).collect::<Result<_>>()?,
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
