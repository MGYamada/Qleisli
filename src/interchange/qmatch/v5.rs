//! Version 5 transport preparation. These readers and writers issue no handle;
//! production dispatch remains at the prior profile until all body obligations
//! and the paired fresh native comparison are connected.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;

pub const PROFILE: &str = "finite-source-qmatch-context-v5";

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Source {
    pub module: String,
    pub function: String,
    pub arguments: StaticArguments,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Request {
    pub source: Source,
    pub context: Context,
}

impl Source {
    fn bounded(&self, remaining: &mut usize) -> Result<()> {
        if self.module.is_empty() || self.function.is_empty() || self.module.len() > 4096 || self.function.len() > 4096 {
            return Err(Error::format("qmatch source name capacity"));
        }
        charge(remaining, (self.module.len()+self.function.len()).saturating_mul(6).saturating_add(512))?;
        self.arguments.bounded(remaining)
    }
    fn encode(&self) -> Value {
        Value::object([
            ("module", text(&self.module)), ("function", text(&self.function)),
            ("static_bases", operations::encode_bases(&self.arguments.bases)),
            ("static_naturals", operations::encode_naturals(&self.arguments.naturals)),
            ("static_operations", self.arguments.operations_value()),
        ])
    }
    fn decode(value: &Value) -> Result<Self> {
        value.fields(&["module", "function", "static_bases", "static_naturals", "static_operations"])?;
        Ok(Self {
            module:value.field("module")?.text()?.into(), function:value.field("function")?.text()?.into(),
            arguments:StaticArguments::decode(value)?,
        })
    }
}

impl Request {
    fn bounded(&self) -> Result<()> {
        let mut remaining = json::MAX_BYTES;
        self.source.bounded(&mut remaining)?;
        self.context.bounded(0, &mut remaining)
    }
    pub fn encode(&self) -> Result<Vec<u8>> {
        self.bounded()?;
        let mut fields = vec![
            ("format".into(), text("qleisli.qmatch-request")), ("version".into(), n(5)),
            ("profile".into(), text(PROFILE)), ("source".into(), self.source.encode()),
        ];
        fields.extend(self.context.fields());
        json::encode(&Value::object(fields))
    }
    pub fn decode(bytes: &[u8]) -> Result<Self> {
        let value = json::parse(bytes)?;
        value.fields(&["format", "version", "profile", "source", "positions", "sites", "calls", "bodies"])?;
        if value.field("format")?.text()? != "qleisli.qmatch-request" || value.field("version")?.number()? != 5
            || value.field("profile")?.text()? != PROFILE {
            return Err(Error::format("unsupported qmatch request profile"));
        }
        let mut remaining = json::MAX_BYTES;
        let request = Self {
            source:Source::decode(value.field("source")?)?, context:Context::decode_fields(&value, 0, &mut remaining)?,
        };
        request.bounded()?;
        Ok(request)
    }
}
