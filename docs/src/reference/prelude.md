# Prelude, imports and qualified names

The ordinary `std::prelude` supplies six derived names by default:
`std::gate::{id,x,z,t,cnot}` and `std::state::init0`. Its public reexports denote
those original declarations, with their existing signatures and contracts.
It defines no forwarding functions, language primitives or verification rule.
The [stdlib contracts](stdlib.md) remain authoritative for their meanings.

## Quick reference

| Form | Behavior |
| --- | --- |
| `x(q)` | Lexical binding, declaration or explicit import first; otherwise the derived prelude X. |
| `use std::gate::x;` | Explicitly import the original public declaration. |
| `use std::prelude::{init0,cnot};` | Explicitly import original targets through public reexports. |
| `std::gate::x(q)` | Select a root-qualified ordinary declaration, checking its original visibility and category. |
| `id[type((Bit,Bit))]` | Apply to an owner with this complete Basis tree; prelude membership infers no static argument. |
| `#![no_implicit_prelude]` | Leading module header: disable only implicit derived-prelude lookup. |
| `pub use gates::x;` | Publicly reexport the original public `gates::x`, without a wrapper or new effect. |
| `h(q)`, `measure_z(q)`, `split(q)`, `join(a,b)` | Bare language primitives; unaffected by prelude opt-out. |

For example, the default prelude permits:

```qli
observe fn main() -> (Bit, Bit) {
    let (a, b) = cnot(h(init0()), init0());
    (measure_z(a), measure_z(b))
}
```

The explicit form is:

```qli
#![no_implicit_prelude]

use std::gate::cnot;
use std::state::init0;

observe fn main() -> (Bit, Bit) {
    let (a, b) = cnot(h(init0()), init0());
    (measure_z(a), measure_z(b))
}
```

Both forms undergo the same source and independent native checks. Names supply
no ownership, effect, inverse, control, Meaning or cleanup permission.

## Lookup and explicit mode

Unqualified references resolve in this order:

1. The original lexical runtime/static binding, including a consumed owner or
   a binding of the wrong category.
2. A same-module declaration or explicit import. Their existing duplicate and
   declaration collisions reject; they do not form an overload set.
3. An original declaration selected by the implicit derived prelude, unless
   this module has opted out.
4. A genuinely unbound bare language primitive.

Lexical bindings and explicit imports precede the prelude, following Rust's
ordinary-name model. Qleisli retains its own canonical declaration table,
quantum contracts and separate bare-primitive boundary.

A failed type, static arity, owner, effect, access, concrete-profile or native
check never retries another tier. A local or explicitly imported identity named
`x` therefore keeps its identity behavior; a runtime value named `x` is not
callable and cannot fall back to the prelude gate.

The single supported header `#![no_implicit_prelude]` may occur once before
imports and declarations. Comments and whitespace may precede it. It introduces
no general attribute or macro facility. It disables only implicit opening;
explicit imports, public reexports, root-qualified references and bare language
primitives remain available. The same rule applies to each source module and
both common frontend consumers.

## Public reexports and qualification

`pub use module::item;` and brace groups expose the original public declaration.
Reexport chains retain its canonical declaration identity, original source
dependencies, visibility, category and caller-visible public effect. A facade
cannot expose a private target or sharpen an external Observe contract using
the target's more precise same-module inference.

Exports resolve over the complete module table, independently of file order.
Duplicate imports and clashes with local declarations reject. An unanchored
public reexport cycle rejects; unused ordinary import-only cycles remain
permitted. `as`, glob imports, relative imports, runtime module initialization
and import-time effects are unsupported.

Root-qualified references such as `std::gate::x` and `library::Meaning` use the
same canonical table. Their ordinary static arguments remain explicit. External
access requires the original public declaration; same-module private access
remains allowed. There is no lexical, prelude or primitive fallback after a
failed qualified selection. Qualified primitive aliases and the retired
foundation paths remain rejected with their migration guidance.

## Compatibility, diagnostics and evidence

Prelude additions must not capture an already resolved program. Lexical names,
declarations and explicit imports keep precedence; the prelude cannot reexport
a bare primitive spelling. Changing an existing selected meaning requires the
ordinary versioned breaking-change and migration process. The fixed member list
is ordinary captured std source, coupled to the selected toolchain.

Malformed or misplaced headers are parse errors. Private qualified targets are
visibility errors; missing modules/members, explicit collisions and export cycles
retain the selected source path and original span. A wrong-category local, moved
owner or missing Basis actual keeps its corresponding existing diagnostic.

The additional eighth bundled module counts toward the unchanged source byte,
module and work limits. Canonical target identity does not erase the implicit
opening or reexport chain from relevant source snapshots. Project source
receipts also include the export chain when the host selects
a reexported `main::main`, even without a reference in a function body.
Selected-source preparation retains its exact entry and operation-binding
selectors with the original source collection through lowering.
Complete retained source bytes may differ between equivalent forms. Independently
issued evidence
IDs are also distinct: their `Eq` is not a semantic equivalence test.

Bounded conformance compares original canonical targets, independently checked
pure meanings and complete observing instruments, while retaining every actual
artifact and source binding. This establishes its tested scope, not a general
source/runtime preservation theorem or broader QS, PR, RS or EXACT discharge.
