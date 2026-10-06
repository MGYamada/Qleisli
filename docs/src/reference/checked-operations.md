# Checked operations

The current edition-2026 grammar uses
`checked_op(implementation, Meaning)` to request an exact-meaning check for a
source operation. It is a static constructor, used inside the existing
explicit operation arguments. It is not monadic bind, a runtime function value
or constitutional certification. The ordinary naming decision is recorded in
[#82](https://github.com/MGYamada/Qleisli/issues/82).

```text
CheckedOperation ::= checked_op ( Identifier , Identifier )
```

The first identifier names an existing operation; the second resolves to an
existing finite Meaning declaration. Visibility, lexical shadowing, static
premises and exact basis-tree checks apply. Neither argument accepts a runtime
value, a constructed operation expression or an explicitly specialized
provider expression through this form. Existing outer static constructors may
contain the checked operation without changing their own rules.

The common judgment can resolve an in-scope abstract operation formal and
record its pending Meaning-equality obligation. Finite materialization retains
the separate requirement for closed, principal-Unitary source declarations;
it rejects an abstract formal as this constructor's provider. Attaching a
Meaning in the common judgment does not create evidence that bypasses that
downstream refusal.

For example, the following fragment uses the current endomorphic Meaning and
operation-parameter grammar:

```qli
use std::quantum::z;

basis fn z_phase(b: Bit) -> (Bit, (Bit, Bit)) { (0, (0, b)) }
meaning ZMeaning: Bit = phase_by(z_phase);
unitary fn direct(q: Q<Bit>) -> Q<Bit> { z(q) }

unitary fn apply_z[static U: Op<Bit, ZMeaning>](q: Q<Bit>) -> Q<Bit>
requires Apply(U) { U(q) }

unitary fn client(q: Q<Bit>) -> Q<Bit> {
    apply_z[checked_op(direct, ZMeaning)](q)
}
```

The common original-source judgment resolves the operation and Meaning, checks
their exact interface bases and records a pending exact Meaning-equality
obligation. It does not discharge that equality merely by attaching a name.
Finite materialization retains the implementation and its source dependencies
and checks their phase-fixed meaning through the selected native checker before
producing executable evidence. Equal probabilities, equal bit width or equality
up to global phase cannot replace that check. Capability requirements remain
separate: an abstract parameter does not acquire inverse or controlled access
from a Meaning name.

Static descriptions contain no live quantum owner. Applying an operation still
consumes and returns the specified owners; a runtime local, spent value or
captured owner cannot be used as its provider. Separate owners do not imply
separable states, and zero-width owners retain their phase and ownership rules.

The selected concrete projection retains its existing unsupported-static-
constructor refusal. A common source judgment, successful parsing or a pending
obligation does not add concrete lowering, emitter support or native acceptance.
This rename changes no AST meaning, primitive, protocol/schema, checker or
constitutional edition.

## Migration and evidence identity

Replace `bind_op(implementation, Meaning)` with the identical arguments to
`checked_op(implementation, Meaning)`. The old exact word is reserved only for
a located retirement error. It is never accepted as an alias, including in
nested constructors. The [lexical boundary](source-text.md) specifies reserved
identifier collisions, comments, byte spans and diagnostic order.

Retained evidence includes exact source snapshots. Changing this spelling may
therefore change a receipt or QIRF source identity even when its requested
mathematical meaning and ordered interface are unchanged. Reconstruct and
independently check evidence for the migrated source; do not reuse stale
receipts or remove source bindings to force byte equality. Historical first
sources and diagnostics stay unchanged beside explicit current derivatives.

The [operations design candidate](../design/operations.md) proposes broader
arrow and Meaning forms and constructed provider inputs. This naming decision
does not adopt them. The adopted QS, PR, RS and EXACT interpretations, both
scoped QLV1 guarantees and their remaining proof duties retain their recorded
status; this chapter reports no new guarantee or source-preservation theorem.
