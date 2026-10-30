//! Internal full runtime-root metadata. Construction and decoding grant no
//! acceptance, execution, inverse or control access. This is not an external schema.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::carrier::{Atom as BasisAtom, Owner};
use super::json::{self, Value};
use super::ordinary_root::{self, Selection, Storage as OrdinaryStorage};
use super::{Error, Result};
use crate::ir::Effect;

/// Full prefix type. A quantum node retains its complete ordinary basis child.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Atom {
    Finite(BasisAtom),
    Quantum,
}

/// Prefix storage retains outer tuples and every logical owner, including Q<Unit>.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Storage {
    Ordinary(Vec<BasisAtom>, OrdinaryStorage),
    Quantum(Owner),
    Tuple(u32),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Request {
    pub selection: Selection,
    pub module: String,
    pub declaration: String,
    pub parameters: Vec<Vec<Atom>>,
    pub input_storage: Vec<Vec<Storage>>,
    pub input_rows: Vec<Vec<bool>>,
    pub result: Vec<Atom>,
    pub storage: Vec<Storage>,
    pub public_effect: Effect,
}

fn text(value: impl Into<String>) -> Value {
    Value::String(value.into())
}
fn array<T>(values: &[T], encode: impl Fn(&T) -> Value) -> Value {
    Value::Array(values.iter().map(encode).collect())
}

impl Atom {
    fn encode(&self) -> Value {
        match self {
            Self::Quantum => Value::object([("tag", text("quantum"))]),
            Self::Finite(atom) => Value::object([("tag", text("finite")), ("atom", atom.encode())]),
        }
    }

    fn decode(value: &Value) -> Result<Self> {
        match value.field("tag")?.text()? {
            "quantum" => {
                value.fields(&["tag"])?;
                Ok(Self::Quantum)
            }
            "finite" => {
                value.fields(&["tag", "atom"])?;
                Ok(Self::Finite(BasisAtom::decode(value.field("atom")?)?))
            }
            _ => Err(Error::format("unknown runtime type atom")),
        }
    }
}

impl Storage {
    fn encode(&self) -> Value {
        match self {
            Self::Ordinary(basis, stored) => Value::object([
                ("tag", text("ordinary")),
                ("basis", array(basis, BasisAtom::encode)),
                ("storage", stored.encode()),
            ]),
            Self::Quantum(owner) => {
                Value::object([("tag", text("quantum")), ("owner", owner.encode())])
            }
            Self::Tuple(arity) => Value::object([
                ("tag", text("tuple")),
                ("arity", Value::Number(u64::from(*arity))),
            ]),
        }
    }

    fn decode(value: &Value, ordinary_left: &mut usize) -> Result<Self> {
        Ok(match value.field("tag")?.text()? {
            "ordinary" => {
                value.fields(&["tag", "basis", "storage"])?;
                let atoms = value.field("basis")?.array()?;
                if atoms.len() > 128 {
                    return Err(Error::limit("runtime finite basis capacity"));
                }
                Self::Ordinary(
                    atoms.iter().map(BasisAtom::decode).collect::<Result<_>>()?,
                    OrdinaryStorage::decode(value.field("storage")?, 0, ordinary_left)?,
                )
            }
            "quantum" => {
                value.fields(&["tag", "owner"])?;
                Self::Quantum(Owner::decode(value.field("owner")?)?)
            }
            "tuple" => {
                value.fields(&["tag", "arity"])?;
                Self::Tuple(
                    u32::try_from(value.field("arity")?.number()?)
                        .map_err(|_| Error::format("runtime arity exceeds u32"))?,
                )
            }
            _ => return Err(Error::format("unknown runtime storage atom")),
        })
    }
}

fn tree(value: &Value, left: &mut usize) -> Result<Vec<Atom>> {
    let atoms = value.array()?;
    *left = left
        .checked_sub(atoms.len())
        .ok_or_else(|| Error::limit("runtime type capacity"))?;
    atoms.iter().map(Atom::decode).collect()
}

fn storage(value: &Value, nodes: &mut usize, ordinary: &mut usize) -> Result<Vec<Storage>> {
    let atoms = value.array()?;
    *nodes = nodes
        .checked_sub(atoms.len())
        .ok_or_else(|| Error::limit("runtime storage capacity"))?;
    atoms
        .iter()
        .map(|atom| Storage::decode(atom, ordinary))
        .collect()
}

impl Request {
    pub fn encode(&self) -> Result<Vec<u8>> {
        self.preflight()?;
        json::encode(&Value::object([
            ("format", text("qleisli.runtime-root-request")),
            ("version", Value::Number(1)),
            ("profile", text("finite-runtime-root-v1")),
            ("selection", text(self.selection.name())),
            ("module", text(&self.module)),
            ("declaration", text(&self.declaration)),
            (
                "parameters",
                array(&self.parameters, |tree| array(tree, Atom::encode)),
            ),
            (
                "input_storage",
                array(&self.input_storage, |tree| array(tree, Storage::encode)),
            ),
            (
                "input_rows",
                array(&self.input_rows, |row| array(row, |bit| Value::Bool(*bit))),
            ),
            ("result", array(&self.result, Atom::encode)),
            ("storage", array(&self.storage, Storage::encode)),
            (
                "public_effect",
                text(match self.public_effect {
                    Effect::Unitary => "unitary",
                    Effect::Isometry => "isometry",
                    Effect::Observe => "observe",
                }),
            ),
        ]))
    }

    pub(super) fn preflight(&self) -> Result<()> {
        if self.parameters.len() > 64
            || self.input_storage.len() > 64
            || self.input_rows.len() > 64
            || self.input_rows.iter().any(|row| row.len() > 6)
        {
            return Err(Error::limit("runtime input forest or row capacity"));
        }
        if self.result.len() > 384
            || self.storage.len() > 384
            || self.parameters.iter().map(Vec::len).sum::<usize>() > 384
            || self.input_storage.iter().map(Vec::len).sum::<usize>() > 384
        {
            return Err(Error::limit("runtime type or storage capacity"));
        }
        for node in self.input_storage.iter().flatten().chain(&self.storage) {
            let basis = match node {
                Storage::Ordinary(basis, _) => basis,
                Storage::Quantum(owner) => &owner.basis,
                Storage::Tuple(_) => continue,
            };
            if basis.len() > 128 {
                return Err(Error::limit("runtime finite basis capacity"));
            }
        }
        fn ordinary(node: &Storage) -> Option<&OrdinaryStorage> {
            match node {
                Storage::Ordinary(_, stored) => Some(stored),
                _ => None,
            }
        }
        ordinary_root::Request::storage_preflight(
            self.input_storage.iter().flatten().filter_map(ordinary),
        )?;
        ordinary_root::Request::storage_preflight(self.storage.iter().filter_map(ordinary))
    }

    pub fn decode(bytes: &[u8]) -> Result<Self> {
        let value = json::parse(bytes)?;
        value.fields(&[
            "format",
            "version",
            "profile",
            "selection",
            "module",
            "declaration",
            "parameters",
            "input_storage",
            "input_rows",
            "result",
            "storage",
            "public_effect",
        ])?;
        if value.field("format")?.text()? != "qleisli.runtime-root-request"
            || value.field("version")?.number()? != 1
            || value.field("profile")?.text()? != "finite-runtime-root-v1"
        {
            return Err(Error::format("unsupported runtime root request"));
        }
        let parameters = value.field("parameters")?.array()?;
        let inputs = value.field("input_storage")?.array()?;
        let rows = value.field("input_rows")?.array()?;
        if parameters.len() > 64 || inputs.len() > 64 || rows.len() > 64 {
            return Err(Error::limit("runtime input forest or row capacity"));
        }
        let (mut type_left, mut storage_left, mut ordinary_left) = (384, 384, 128);
        let result = Self {
            selection: match value.field("selection")?.text()? {
                "project" => Selection::Project,
                "exported" => Selection::Exported,
                "internal" => Selection::Internal,
                _ => return Err(Error::format("unknown runtime entry selection")),
            },
            module: value.field("module")?.text()?.into(),
            declaration: value.field("declaration")?.text()?.into(),
            parameters: parameters
                .iter()
                .map(|value| tree(value, &mut type_left))
                .collect::<Result<_>>()?,
            input_storage: inputs
                .iter()
                .map(|value| storage(value, &mut storage_left, &mut ordinary_left))
                .collect::<Result<_>>()?,
            input_rows: rows
                .iter()
                .map(|row| {
                    let values = row.array()?;
                    if values.len() > 6 {
                        return Err(Error::limit("runtime input row width"));
                    }
                    values
                        .iter()
                        .map(Value::boolean)
                        .collect::<Result<Vec<_>>>()
                })
                .collect::<Result<_>>()?,
            result: tree(value.field("result")?, &mut 384)?,
            storage: storage(value.field("storage")?, &mut 384, &mut 128)?,
            public_effect: match value.field("public_effect")?.text()? {
                "unitary" => Effect::Unitary,
                "isometry" => Effect::Isometry,
                "observe" => Effect::Observe,
                _ => return Err(Error::format("unknown runtime public effect")),
            },
        };
        result.preflight()?;
        Ok(result)
    }
}
