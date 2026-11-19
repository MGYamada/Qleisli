# Prelude, imports and qualified names

The **prelude** is the ordinary module `std::prelude`. It makes six derived
names available in every module without an import:
`std::gate::{id,x,z,t,cnot}` and `std::state::init0`. Each name is a public
reexport that denotes the original declaration, with its signature and its
contract. The prelude defines no forwarding function, no language primitive
and no verification rule. The [stdlib contracts](stdlib.md) are authoritative
for the meanings of the six names.

This chapter gives the lookup order of unqualified names, the
`#![no_implicit_prelude]` header, public reexports and qualified names.

## Quick reference

| Form | Behavior |
| --- | --- |
| `x(q)` | Lexical binding, declaration or explicit import first; otherwise the derived prelude X. |
| `use std::gate::x;` | Explicitly import the original public declaration. |
| `use std::prelude::{init0,cnot};` | Explicitly import original targets through public reexports. |
| `std::gate::x(q)` | Select a root-qualified ordinary declaration, checking its original visibility and category. |
| `id[type((Bit,Bit))]` | Apply to an owner with this complete Basis tree; prelude membership infers no static argument. |
| `#![no_implicit_prelude]` | Leading module header: disable only implicit derived-prelude lookup. |
| `pub use gates::x;` | Publicly reexport the original public `gates::x`, without a wrapper or an added effect. |
| `h(q)`, `measure_z(q)`, `split(q)`, `join(a,b)` | Bare language primitives; unaffected by prelude opt-out. |

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

Both forms undergo the same source checks and the same independent native
checks. A name supplies no ownership, effect, inverse, control, Meaning or
cleanup permission.

## Lookup order

An unqualified reference resolves to the first of these that applies:

1. The original lexical runtime or static binding. This includes a consumed
   owner and a binding of the wrong category.
2. A declaration of the same module, or an explicit import.
3. An original declaration that the implicit prelude selects, unless the
   module has opted out.
4. A bare language primitive, where nothing else binds the name.

Lexical bindings and explicit imports precede the prelude, as in Rust's
ordinary-name model. Qleisli keeps its own canonical declaration table, its
quantum contracts and its separate boundary for bare primitives.

Rules:

- A declaration and an explicit import of the same name do not form an
  overload set. A duplicate or a collision between them is an error.
- A failed type, static arity, owner, effect, access, concrete-profile or
  native check never retries another tier.
- A local or explicitly imported identity named `x` therefore keeps its
  identity behavior. A runtime value named `x` is not callable, and it does
  not fall back to the prelude gate.

## The `#![no_implicit_prelude]` header

The header disables the implicit opening of the prelude for one module. It is
the single supported header.

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

`pub use module::item;`, and the form with a brace group, exposes the original
public declaration.

Rules:

- A reexport chain retains the canonical declaration identity, the original
  source dependencies, the visibility, the category and the caller-visible
  public effect of its target.
- A facade must not expose a private target.
- A facade must not sharpen an external Observe contract by using the more
  precise inference that the target has inside its own module.
- Exports resolve over the complete module table, independently of file order.
- A duplicate import is an error. An import that clashes with a local
  declaration is an error.
- An unanchored public reexport cycle is an error. An unused cycle of ordinary
  imports is permitted.
- `as`, glob imports, relative imports, runtime module initialization and
  import-time effects are unsupported.

## Qualified names

A root-qualified reference, such as `std::gate::x` or `library::Meaning`, uses
the same canonical declaration table.

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
- Canonical target identity does not erase the implicit opening or the
  reexport chain from the relevant source snapshots.
- Project source receipts include the export chain when the host selects a
  reexported `main::main`, even without a reference in a function body.
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
