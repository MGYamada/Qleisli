//! Original operation actuals are untrusted finite descriptions. Provider
//! arguments retain every child, including unused operation formals.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct StaticArguments {
    pub bases: Vec<(String, Vec<Atom>)>,
    pub naturals: Vec<(String, u32)>,
    pub operations: Vec<(String, Description)>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Description {
    pub nodes: Vec<OperationNode>,
    pub root: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum OperationNode {
    Provider {
        module: String,
        function: String,
        bases: Vec<(String, Vec<Atom>)>,
        naturals: Vec<(String, u32)>,
        operations: Vec<(String, u32)>,
    },
    Formal {
        module: String,
        function: String,
        bases: Vec<(String, Vec<Atom>)>,
        naturals: Vec<(String, u32)>,
        operations: Vec<(String, u32)>,
        ordinal: u32,
    },
    Inverse(u32),
    Then(u32, u32),
    Tensor(u32, u32),
    Controlled(u32),
    Power { child: u32, count: u32 },
    Conjugate { outer: u32, middle: u32 },
}

fn basis(value: &Value) -> Result<Vec<Atom>> {
    let atoms = value.array()?;
    if atoms.len() > 128 {
        return Err(Error::limit("qmatch static basis capacity"));
    }
    atoms.iter().map(Atom::decode).collect()
}

pub(super) fn bases(value: &Value) -> Result<Vec<(String, Vec<Atom>)>> {
    value.array()?.iter().map(|value| {
        value.fields(&["name", "basis"])?;
        Ok((value.field("name")?.text()?.into(), basis(value.field("basis")?)?))
    }).collect()
}

pub(super) fn naturals(value: &Value) -> Result<Vec<(String, u32)>> {
    value.array()?.iter().map(|value| {
        value.fields(&["name", "value"])?;
        Ok((value.field("name")?.text()?.into(), number(value.field("value")?)?))
    }).collect()
}

pub(super) fn encode_bases(values: &[(String, Vec<Atom>)]) -> Value {
    Value::Array(values.iter().map(|(name, basis)| Value::object([
        ("name", text(name)), ("basis", Value::Array(basis.iter().map(Atom::encode).collect()))
    ])).collect())
}

pub(super) fn encode_naturals(values: &[(String, u32)]) -> Value {
    Value::Array(values.iter().map(|(name, value)| Value::object([
        ("name", text(name)), ("value", n(*value))
    ])).collect())
}

fn name_storage(value: &str, remaining: &mut usize) -> Result<()> {
    if value.is_empty() || value.len() > 4096 {
        return Err(Error::format("qmatch static name capacity"));
    }
    charge(remaining, value.len().saturating_mul(6).saturating_add(32))
}

fn scalar_arguments_storage(bases: &[(String, Vec<Atom>)], naturals: &[(String,u32)], count: usize,
    remaining: &mut usize) -> Result<()> {
    if bases.len().saturating_add(naturals.len()).saturating_add(count) > 32 {
        return Err(Error::limit("qmatch static argument capacity"));
    }
    for (name, basis) in bases {
        name_storage(name, remaining)?;
        basis_storage(basis, remaining)?;
    }
    for (name, _) in naturals {
        name_storage(name, remaining)?;
        charge(remaining, 32)?;
    }
    Ok(())
}

impl StaticArguments {
    pub(super) fn bounded(&self, remaining: &mut usize) -> Result<()> {
        scalar_arguments_storage(&self.bases, &self.naturals, self.operations.len(), remaining)?;
        for (name, description) in &self.operations {
            name_storage(name, remaining)?;
            description.bounded(remaining)?;
        }
        Ok(())
    }

    pub(super) fn operations_value(&self) -> Value {
        Value::Array(self.operations.iter().map(|(name, description)| Value::object([
            ("name", text(name)), ("description", description.encode())
        ])).collect())
    }

    pub(super) fn decode(value: &Value) -> Result<Self> {
        let b = value.field("static_bases")?.array()?;
        let n = value.field("static_naturals")?.array()?;
        let o = value.field("static_operations")?.array()?;
        if b.len().saturating_add(n.len()).saturating_add(o.len()) > 32 {
            return Err(Error::limit("qmatch static argument capacity"));
        }
        Ok(Self {
            bases: bases(value.field("static_bases")?)?,
            naturals: naturals(value.field("static_naturals")?)?,
            operations: o.iter().map(|value| {
                value.fields(&["name", "description"])?;
                Ok((value.field("name")?.text()?.into(), Description::decode(value.field("description")?)?))
            }).collect::<Result<_>>()?,
        })
    }
}

impl Description {
    pub(super) fn bounded(&self, remaining: &mut usize) -> Result<()> {
        if self.nodes.is_empty() || self.nodes.len() > 4096 {
            return Err(Error::limit("qmatch operation description capacity"));
        }
        charge(remaining, self.nodes.len().saturating_mul(128))?;
        for node in &self.nodes {
            if let OperationNode::Provider { module,function,bases,naturals,operations }
                | OperationNode::Formal { module,function,bases,naturals,operations,.. } = node {
                name_storage(module, remaining)?;
                name_storage(function, remaining)?;
                scalar_arguments_storage(bases, naturals, operations.len(), remaining)?;
                for (name, _) in operations { name_storage(name, remaining)?; }
            }
        }
        Ok(())
    }

    fn encode(&self) -> Value {
        Value::object([("nodes", Value::Array(self.nodes.iter().map(OperationNode::encode).collect())), ("root", n(self.root))])
    }

    fn decode(value: &Value) -> Result<Self> {
        value.fields(&["nodes", "root"])?;
        let nodes = value.field("nodes")?.array()?;
        if nodes.is_empty() || nodes.len() > 4096 {
            return Err(Error::limit("qmatch operation description capacity"));
        }
        Ok(Self { nodes: nodes.iter().map(OperationNode::decode).collect::<Result<_>>()?, root: number(value.field("root")?)? })
    }
}

impl OperationNode {
    fn encode(&self) -> Value {
        match self {
            Self::Provider { module,function,bases,naturals,operations } => Value::object([
                ("tag", text("provider")), ("module", text(module)), ("function", text(function)),
                ("static_bases", encode_bases(bases)), ("static_naturals", encode_naturals(naturals)),
                ("static_operations", Value::Array(operations.iter().map(|(name,node)| Value::object([
                    ("name", text(name)), ("node", n(*node))
                ])).collect())),
            ]),
            Self::Formal { module,function,bases,naturals,operations,ordinal } => Value::object([
                ("tag", text("formal")), ("module", text(module)), ("function", text(function)),
                ("static_bases", encode_bases(bases)), ("static_naturals", encode_naturals(naturals)),
                ("static_operations", Value::Array(operations.iter().map(|(name,node)| Value::object([
                    ("name", text(name)), ("node", n(*node))
                ])).collect())), ("ordinal", n(*ordinal)),
            ]),
            Self::Inverse(child) => Value::object([("tag", text("inverse")), ("child", n(*child))]),
            Self::Controlled(child) => Value::object([("tag", text("controlled")), ("child", n(*child))]),
            Self::Then(left,right) => Value::object([("tag", text("then")), ("left", n(*left)), ("right", n(*right))]),
            Self::Tensor(left,right) => Value::object([("tag", text("tensor")), ("left", n(*left)), ("right", n(*right))]),
            Self::Power { child,count } => Value::object([("tag", text("power")), ("child", n(*child)), ("count", n(*count))]),
            Self::Conjugate { outer,middle } => Value::object([("tag", text("conjugate")), ("outer", n(*outer)), ("middle", n(*middle))]),
        }
    }

    fn decode(value: &Value) -> Result<Self> {
        let get = |field| number(value.field(field)?);
        Ok(match value.field("tag")?.text()? {
            tag @ ("provider" | "formal") => {
                if tag == "formal" {
                    value.fields(&["tag", "module", "function", "static_bases", "static_naturals", "static_operations", "ordinal"])?;
                } else {
                    value.fields(&["tag", "module", "function", "static_bases", "static_naturals", "static_operations"])?;
                }
                let operations = value.field("static_operations")?.array()?;
                let b = value.field("static_bases")?.array()?;
                let n = value.field("static_naturals")?.array()?;
                if b.len().saturating_add(n.len()).saturating_add(operations.len()) > 32 {
                    return Err(Error::limit("qmatch static argument capacity"));
                }
                let module = value.field("module")?.text()?.into();
                let function = value.field("function")?.text()?.into();
                let bases = bases(value.field("static_bases")?)?;
                let naturals = naturals(value.field("static_naturals")?)?;
                let operations = operations.iter().map(|value| {
                        value.fields(&["name", "node"])?;
                        Ok((value.field("name")?.text()?.into(), number(value.field("node")?)?))
                    }).collect::<Result<_>>()?;
                if tag == "formal" {
                    Self::Formal { module,function,bases,naturals,operations,ordinal:get("ordinal")? }
                } else {
                    Self::Provider { module,function,bases,naturals,operations }
                }
            }
            "inverse" => { value.fields(&["tag", "child"])?; Self::Inverse(get("child")?) }
            "controlled" => { value.fields(&["tag", "child"])?; Self::Controlled(get("child")?) }
            "then" => { value.fields(&["tag", "left", "right"])?; Self::Then(get("left")?, get("right")?) }
            "tensor" => { value.fields(&["tag", "left", "right"])?; Self::Tensor(get("left")?, get("right")?) }
            "power" => { value.fields(&["tag", "child", "count"])?; Self::Power { child:get("child")?, count:get("count")? } }
            "conjugate" => { value.fields(&["tag", "outer", "middle"])?; Self::Conjugate { outer:get("outer")?, middle:get("middle")? } }
            _ => return Err(Error::format("unknown qmatch operation node")),
        })
    }
}
