//! Independent v5 walker over the retained graph and typed request. There is
//! no JSON replay, native dispatcher or accepted-handle constructor here.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::interchange::qmatch::{self as data, v5::Request};
use crate::interchange::carrier::Atom;

fn bases(view: &mut View<'_>, values: &[(String, Vec<Atom>)]) -> Result<()> {
    view.list(values, |w, (name,basis)| w.record("source-static-basis", 2, |w| {
        w.writer.text(name)?;
        w.list(basis, carrier::atom)
    }))
}

fn naturals(view: &mut View<'_>, values: &[(String,u32)]) -> Result<()> {
    view.list(values, |w, (name,value)| w.record("source-static-natural", 2, |w| {
        w.writer.text(name)?;
        w.n(*value as usize)
    }))
}

fn references(view: &mut View<'_>, values: &[(String,u32)]) -> Result<()> {
    view.list(values, |w, (name,node)| w.record("source-operation-reference", 2, |w| {
        w.writer.text(name)?;
        w.n(*node as usize)
    }))
}

fn node(view: &mut View<'_>, value: &data::OperationNode) -> Result<()> {
    use data::OperationNode::*;
    match value {
        Primitive { kind,target } => view.record("source-operation-primitive", 2, |w| {
            w.writer.text(kind.name())?;
            w.list(target, carrier::atom)
        }),
        Provider { module,function,bases:b,naturals:n,operations } => view.record("source-operation-provider", 5, |w| {
            w.writer.text(module)?;
            w.writer.text(function)?;
            bases(w,b)?;
            naturals(w,n)?;
            references(w,operations)
        }),
        Formal { module,function,bases:b,naturals:n,operations,ordinal } => view.record("source-operation-formal", 6, |w| {
            w.writer.text(module)?;
            w.writer.text(function)?;
            bases(w,b)?;
            naturals(w,n)?;
            references(w,operations)?;
            w.n(*ordinal as usize)
        }),
        Inverse(child) => view.record("source-operation-inverse", 1, |w| w.n(*child as usize)),
        Controlled(child) => view.record("source-operation-controlled", 1, |w| w.n(*child as usize)),
        Then(left,right) => view.record("source-operation-then", 2, |w| {w.n(*left as usize)?;w.n(*right as usize)}),
        Tensor(left,right) => view.record("source-operation-tensor", 2, |w| {w.n(*left as usize)?;w.n(*right as usize)}),
        Power { child,count } => view.record("source-operation-power", 2, |w| {w.n(*child as usize)?;w.n(*count as usize)}),
        Conjugate { outer,middle } => view.record("source-operation-conjugate", 2, |w| {w.n(*outer as usize)?;w.n(*middle as usize)}),
    }
}

fn description(view: &mut View<'_>, value: &data::Description) -> Result<()> {
    view.record("source-operation-description", 2, |w| {
        w.list(&value.nodes, node)?;
        w.n(value.root as usize)
    })
}

fn position(view: &mut View<'_>, value: &data::Position) -> Result<()> {
    view.record("source-interval", 3, |w| {
        w.n(value.offset as usize)?;
        w.n(value.start as usize)?;
        w.n(value.count as usize)
    })
}

fn context(view: &mut View<'_>, value: &data::Context) -> Result<()> {
    view.record("source-context", 4, |w| {
        w.list(&value.positions, position)?;
        w.list(&value.sites, |w, site| w.record("qmatch-site", 4, |w| {
            carrier::interface(w,&site.attached)?;
            carrier::interface(w,&site.required)?;
            position(w,&site.position)?;
            w.list(&site.arms, |w, arm| w.record("qmatch-arm", 3, |w| {
                w.n(arm.implementation as usize)?;
                w.n(arm.controlled as usize)?;
                w.list(&arm.providers, |w, provider| match provider {
                    data::ProviderSubject::Function { evidence } => w.record("qmatch-function-provider", 1, |w| w.n(*evidence as usize)),
                    data::ProviderSubject::Pure { program } => w.record("qmatch-pure-provider", 1, |w| w.n(*program as usize)),
                })
            }))
        }))?;
        w.list(&value.calls, |w, call| w.record("source-call", 2, |w| {
            position(w,&call.position)?;
            context(w,&call.body)
        }))?;
        w.list(&value.bodies, context)
    })
}

pub(in crate::interchange) fn complete(graph: Graph<'_>, request: &Request) -> Result<Vec<u8>> {
    let mut writer = Writer { bytes:b"QDV1".to_vec(), limit:MAX_BYTES, depth:0 };
    writer.sized(5, 4)?;
    writer.depth += 1;
    writer.text(data::v5::PROFILE)?;
    graph.write(&mut writer)?;
    let mut view = View { writer:&mut writer, dependencies:&BTreeMap::new() };
    view.record("source-function", 5, |w| {
        w.writer.text(&request.source.module)?;
        w.writer.text(&request.source.function)?;
        bases(w,&request.source.arguments.bases)?;
        naturals(w,&request.source.arguments.naturals)?;
        w.list(&request.source.arguments.operations, |w, (name,value)| w.record("source-static-operation", 2, |w| {
            w.writer.text(name)?;
            description(w,value)
        }))
    })?;
    context(&mut view,&request.context)?;
    writer.depth -= 1;
    Ok(writer.bytes)
}
