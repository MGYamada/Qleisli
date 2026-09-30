//! Compiler-owned primitive declarations, separate from ordinary `.qli` std.
//!
//! This inventory is used by import resolution and primitive lowering. It does
//! not allow source files to declare or replace primitives. `A` and `B` below
//! are specification metavariables, not new generic source syntax.
//!
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

use super::ast::FnKind;

/// A sealed source signature. Implementations and independent IR checking are
/// still required; this declaration is not executable evidence.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Primitive {
    pub module: &'static str,
    pub name: &'static str,
    pub kind: FnKind,
    pub arity: usize,
    pub signature: &'static str,
}

/// The existing sealed surface, without new source paths or library functions.
pub const PRIMITIVES: &[Primitive] = &[
    Primitive {
        module: "std::quantum",
        name: "init0",
        kind: FnKind::Iso,
        arity: 0,
        signature: "() -> Q<Bit>",
    },
    Primitive {
        module: "std::quantum",
        name: "h",
        kind: FnKind::Unitary,
        arity: 1,
        signature: "(Q<Bit>) -> Q<Bit>",
    },
    Primitive {
        module: "std::quantum",
        name: "x",
        kind: FnKind::Unitary,
        arity: 1,
        signature: "(Q<Bit>) -> Q<Bit>",
    },
    Primitive {
        module: "std::quantum",
        name: "z",
        kind: FnKind::Unitary,
        arity: 1,
        signature: "(Q<Bit>) -> Q<Bit>",
    },
    Primitive {
        module: "std::quantum",
        name: "t",
        kind: FnKind::Unitary,
        arity: 1,
        signature: "(Q<Bit>) -> Q<Bit>",
    },
    Primitive {
        module: "std::quantum",
        name: "cnot",
        kind: FnKind::Unitary,
        arity: 2,
        signature: "(Q<Bit>, Q<Bit>) -> (Q<Bit>, Q<Bit>)",
    },
    Primitive {
        module: "std::quantum",
        name: "toffoli",
        kind: FnKind::Unitary,
        arity: 3,
        signature: "(Q<Bit>, Q<Bit>, Q<Bit>) -> ((Q<Bit>, Q<Bit>), Q<Bit>)",
    },
    Primitive {
        module: "std::quantum",
        name: "split",
        kind: FnKind::Unitary,
        arity: 1,
        signature: "(Q<(A,B)>) -> (Q<A>, Q<B>)",
    },
    Primitive {
        module: "std::quantum",
        name: "join",
        kind: FnKind::Unitary,
        arity: 2,
        signature: "(Q<A>, Q<B>) -> Q<(A,B)>",
    },
    Primitive {
        module: "std::observe",
        name: "measure_z",
        kind: FnKind::Observe,
        arity: 1,
        signature: "(Q<Bit>) -> CBit",
    },
    Primitive {
        module: "std::observe",
        name: "reset",
        kind: FnKind::Observe,
        arity: 1,
        signature: "(Q<Bit>) -> Q<Bit>",
    },
    Primitive {
        module: "std::observe",
        name: "discard",
        kind: FnKind::Observe,
        arity: 1,
        signature: "(Q<A>) -> Unit",
    },
];

pub fn primitive(module: &str, name: &str) -> Option<&'static Primitive> {
    PRIMITIVES
        .iter()
        .find(|item| item.module == module && item.name == name)
}
