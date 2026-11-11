//! Version 5 transport preparation. These readers and writers issue no handle;
//! an execution decision requires the independent native comparison.
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
    /// This is the same typed object retained for public runtime execution.
    pub runtime: std::sync::Arc<crate::interchange::runtime_root::Request>,
    pub context: Context,
}

mod producer;
mod runtime;
pub(crate) use producer::proposal;

impl Source {
    fn bounded(&self, remaining: &mut usize) -> Result<()> {
        if self.module.is_empty()
            || self.function.is_empty()
            || self.module.len() > 4096
            || self.function.len() > 4096
        {
            return Err(Error::format("qmatch source name capacity"));
        }
        charge(
            remaining,
            (self.module.len() + self.function.len())
                .saturating_mul(6)
                .saturating_add(512),
        )?;
        self.arguments.bounded(remaining)
    }
    fn encode(&self) -> Value {
        Value::object([
            ("module", text(&self.module)),
            ("function", text(&self.function)),
            (
                "static_bases",
                operations::encode_bases(&self.arguments.bases),
            ),
            (
                "static_naturals",
                operations::encode_naturals(&self.arguments.naturals),
            ),
            ("static_operations", self.arguments.operations_value()),
        ])
    }
    fn decode(value: &Value) -> Result<Self> {
        value.fields(&[
            "module",
            "function",
            "static_bases",
            "static_naturals",
            "static_operations",
        ])?;
        Ok(Self {
            module: value.field("module")?.text()?.into(),
            function: value.field("function")?.text()?.into(),
            arguments: StaticArguments::decode(value)?,
        })
    }
}

impl Request {
    /// Collect reachability roots from independently typed program/evidence
    /// indices. Ordered occurrences still participate separately in the QDV.
    pub(in crate::interchange) fn graph_roots(
        &self,
        root: usize,
        programs: usize,
        evidence: usize,
    ) -> Result<Vec<usize>> {
        use super::ProviderSubject;
        self.bounded()?;
        let program = |index: u32| {
            let index = index as usize;
            if index < programs {
                Ok(index)
            } else {
                Err(Error::format("missing original qmatch program"))
            }
        };
        let mut roots = std::collections::BTreeSet::from([root]);
        let mut contexts = vec![&self.context];
        while let Some(context) = contexts.pop() {
            for arm in context.sites.iter().flat_map(|site| &site.arms) {
                roots.insert(program(arm.implementation)?);
                roots.insert(program(arm.controlled)?);
            }
            for body in context
                .bodies
                .iter()
                .chain(context.references.iter().flatten().flatten())
            {
                let index = match body.subject {
                    ProviderSubject::Pure { program: index } => program(index)?,
                    ProviderSubject::Function { evidence: index }
                        if (index as usize) < evidence =>
                    {
                        programs + index as usize
                    }
                    ProviderSubject::Function { .. } => {
                        return Err(Error::format("missing original qmatch evidence"));
                    }
                };
                roots.insert(index);
                contexts.push(&body.body);
            }
            contexts.extend(context.calls.iter().map(|call| &call.body));
            for branch in &context.branches {
                contexts.push(&branch.then_body);
                contexts.push(&branch.else_body);
            }
        }
        Ok(roots.into_iter().collect())
    }

    pub(in crate::interchange) fn bounded(&self) -> Result<()> {
        let mut remaining = json::MAX_BYTES;
        self.source.bounded(&mut remaining)?;
        runtime::bounded(&self.runtime, &mut remaining)?;
        if self.source.module != self.runtime.module
            || self.source.function != self.runtime.declaration
            || self.source.arguments.bases != self.runtime.static_bases
            || self.source.arguments.naturals != self.runtime.static_naturals
        {
            return Err(Error::format(
                "qmatch source and retained runtime instance differ",
            ));
        }
        self.context.bounded(0, &mut remaining)
    }
    pub fn encode(&self) -> Result<Vec<u8>> {
        self.bounded()?;
        let mut fields = vec![
            ("format".into(), text("qleisli.qmatch-request")),
            ("version".into(), n(5)),
            ("profile".into(), text(PROFILE)),
            ("source".into(), self.source.encode()),
            ("runtime".into(), self.runtime.value()?),
        ];
        fields.extend(self.context.fields());
        json::encode(&Value::object(fields))
    }
    pub fn decode(bytes: &[u8]) -> Result<Self> {
        let value = json::parse(bytes)?;
        Context::validate_fields(
            &value,
            &["format", "version", "profile", "source", "runtime"],
        )?;
        if value.field("format")?.text()? != "qleisli.qmatch-request"
            || value.field("version")?.number()? != 5
            || value.field("profile")?.text()? != PROFILE
        {
            return Err(Error::format("unsupported qmatch request profile"));
        }
        let mut remaining = json::MAX_BYTES;
        let request = Self {
            source: Source::decode(value.field("source")?)?,
            runtime: std::sync::Arc::new(crate::interchange::runtime_root::Request::decode_value(
                value.field("runtime")?,
            )?),
            context: Context::decode_fields(&value, 0, &mut remaining)?,
        };
        request.bounded()?;
        Ok(request)
    }
}

#[cfg(test)]
mod tests;
