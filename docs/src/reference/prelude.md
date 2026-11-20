# Prelude, imports and qualified names

The **prelude** is the ordinary module `std::prelude`. Every module can use
its names without an import. It holds six derived names:
`std::gate::{id,x,z,t,cnot}` and `std::state::init0`.

The prelude adds nothing of its own. Each name is a public reexport, so `x`
in your module is the original declaration `std::gate::x`, with its signature
and its contract. The prelude defines no forwarding function, no language
primitive and no verification rule. The [stdlib contracts](stdlib.md) are
authoritative for the meanings of the six names.

This chapter explains how the checker finds the declaration behind a name.
It covers the lookup order of unqualified names, the
`#![no_implicit_prelude]` header, public reexports and qualified names.
To try an import in a small project, [move the Bell circuit into a
module](../learn/functions-and-modules.md#move-the-function-into-a-module)
and use the compiler's visibility diagnostic to finish the move.

## Quick reference

| Form | Behavior |
| --- | --- |
| `x(q)` | Uses a lexical binding, a declaration or an explicit import if one exists. Otherwise it is the derived prelude X. |
| `use std::gate::x;` | Imports the original public declaration explicitly. |
| `use std::prelude::{init0,cnot};` | Imports the original targets explicitly, through the public reexports. |
| `std::gate::x(q)` | Selects an ordinary declaration by its path from the root. The checker checks the original visibility and category. |
| `id[type((Bit,Bit))]` | Applies to an owner with this complete Basis tree. Being in the prelude infers no static argument. |
| `#![no_implicit_prelude]` | A header at the top of a module. It turns off the implicit lookup in the derived prelude and nothing else. |
| `pub use gates::x;` | Reexports the original public `gates::x`. It adds no wrapper and no effect. |
| `h(q)`, `measure_z(q)`, `split(q)`, `join(a,b)` | Bare language primitives. The prelude opt-out does not affect them. |

The checker accepts this program with the default prelude:

```qli
observe fn main() -> (Bit, Bit) {
    let (a, b) = cnot(h(init0()), init0());
    (measure_z(a), measure_z(b))
}
```

The checker accepts the same program in the explicit form:

```qli
#![no_implicit_prelude]

use std::gate::cnot;
use std::state::init0;

observe fn main() -> (Bit, Bit) {
    let (a, b) = cnot(h(init0()), init0());
    (measure_z(a), measure_z(b))
}
```

The two forms differ only in how the names are found. Both undergo the same
source checks and the same independent native checks. A name is only a name:
it supplies no ownership, effect, inverse, control, Meaning or cleanup
permission.

## Lookup order

An **unqualified** reference is a name written without a path, such as `x`.
The checker looks in four places, in this order, and takes the first one
that applies:

1. The original lexical binding, whether runtime or static. A binding is
   found here even when its owner is consumed or its category is wrong for
   the use.
2. A declaration of the same module, or an explicit import.
3. An original declaration that the implicit prelude selects, unless the
   module has opted out.
4. A bare language primitive, where nothing else binds the name.

Lexical bindings and explicit imports come before the prelude, as in Rust's
ordinary-name model. Qleisli keeps three things of its own: its canonical
declaration table, its quantum contracts and its separate boundary for bare
primitives.

Rules:

- A declaration and an explicit import of the same name do not form an
  overload set. A duplicate or a collision between them is an error.
- The search ends at the first place that applies. When the selected
  declaration then fails a check, the checker reports that failure and never
  retries another tier. This holds for a failed type, static arity, owner,
  effect, access, concrete-profile or native check.
- A local or explicitly imported identity named `x` therefore keeps its
  identity behavior. A runtime value named `x` is not callable, and it does
  not fall back to the prelude gate.

## The `#![no_implicit_prelude]` header

Write this header when a module should name everything it uses. The header
disables the implicit opening of the prelude for that one module. It is the
single supported header.

Rules:

- The header may occur once, before the imports and declarations of the
  module. Comments and whitespace may precede it.
- A malformed or misplaced header is a parse error.
- The header disables only the implicit opening. Explicit imports, public
  reexports, root-qualified references and bare language primitives stay
  available.
- The header introduces no general attribute or macro facility.
- The same rule applies to each source module and to both common frontend
  consumers.

## Public reexports

A **reexport** makes a declaration from one module available under the name
of another. `pub use module::item;`, and the form with a brace group, exposes
the original public declaration. The reexport is a second path to the same
declaration. It is not a copy and not a wrapper.

Rules:

- A reexport chain retains everything about its target: the canonical
  declaration identity, the original source dependencies, the visibility,
  the category and the caller-visible public effect.
- A facade must not expose a private target.
- Inside its own module, a target can have a more precise inferred effect
  than the one it declares to callers. A facade must not use that inference
  to sharpen an external Observe contract.
- Exports resolve over the complete module table, independently of file order.
- A duplicate import is an error. An import that clashes with a local
  declaration is an error.
- An unanchored public reexport cycle is an error. An unused cycle of ordinary
  imports is permitted.
- `as`, glob imports, relative imports, runtime module initialization and
  import-time effects are unsupported.

## Qualified names

A **root-qualified** reference spells out the path from the root, as in
`std::gate::x` or `library::Meaning`. It uses the same canonical declaration
table as an unqualified name. The path leaves the checker one place to look.

Rules:

- The ordinary static arguments of a qualified reference stay explicit.
- Access from another module requires the original public declaration. A
  private target there is a visibility error. Access to a private declaration
  of the same module is allowed.
- After a failed qualified selection there is no lexical, prelude or primitive
  fallback.
- Qualified primitive aliases and the retired foundation paths are rejected
  with their migration guidance.

## Compatibility

Adding a name to the prelude does not change a program that already
resolves.

Rules:

- An addition to the prelude must not capture an already resolved program.
  Lexical names, declarations and explicit imports keep precedence.
- The prelude cannot reexport a bare primitive spelling.
- A change to an existing selected meaning requires the ordinary versioned
  breaking-change and migration process.
- The member list is ordinary captured std source. It is coupled to the
  selected toolchain.

## Diagnostics

| Failure | Report |
| --- | --- |
| A malformed or misplaced header | A parse error |
| A private qualified target | A visibility error |
| A missing module or member, an explicit collision, or an export cycle | Its diagnostic, with the selected source path and the original span |
| A local of the wrong category, a moved owner, or a missing Basis argument | The diagnostic that the failure has without the prelude |

## Status and limits

- The prelude is the eighth bundled module. It counts toward the unchanged
  source byte, module and work limits.
- Two names with one canonical target are the same declaration. The source
  snapshots keep the implicit opening and the reexport chain all the same.
- When the host selects a reexported `main::main`, the project source
  receipts include the export chain. This holds even without a reference in
  a function body.
- Selected-source preparation retains its entry selector and its
  operation-binding selectors with the original source collection through
  lowering.
- The retained source bytes of two equivalent forms may differ. Independently
  issued evidence IDs are also distinct: their `Eq` is not a semantic
  equivalence test.
- Bounded conformance compares original canonical targets, independently
  checked pure meanings and complete observing instruments. It retains every
  artifact and source binding. This establishes its tested scope. It is not a
  general source or runtime preservation theorem, and it discharges no broader
  QS, PR, RS or EXACT obligation.
