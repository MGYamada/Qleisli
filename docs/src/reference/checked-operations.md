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
downstream refusal. A general `Op<A -> B, M>` formal checks both ports against
the declared basis of the existing endomorphic Meaning; a rectangular arrow
cannot acquire Meaning evidence by dropping its output type. General pure
arrow typing and the current materialization limits are specified in the
[type model](type-model.md#general-pure-operation-arrows).

For example, the following fragment uses the current endomorphic Meaning and
operation-parameter grammar:

```qli
use std::quantum::z;

classical fn z_phase(b: Bit) -> (Bit, (Bit, Bit)) { (0, (0, b)) }
meaning ZMeaning: Bit = phase_by(z_phase);
unitary fn direct(q: Q<Bit>) -> Q<Bit> { z(q) }

unitary fn apply_z[const U: Op<Bit, ZMeaning>](q: Q<Bit>) -> Q<Bit>
requires Applicable(U) { U(q) }

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

The selected concrete projection retains this constructor and its original
Meaning request. Within the supported closed-provider profile,
`ElaboratedProgram::check_operation_meanings` checks original binding requests
and annotated constructor descendants through the native finite gate on their
actual materialized Raw bodies before the checked collection can produce a hierarchy
proposal. That proposal still needs fresh hierarchy acceptance. Direct
unchecked hierarchy or Raw lowering rejects when original Meaning obligations remain.
The checked collection can also emit Raw for direct application, sequential and
tensor composition: independent source replay checks the actual instruction
interval, owner boundary and ordered axes against each original finite request
through a fresh native decision. Unexecuted and zero-repeat child requests are
still checked before emission. Refined Raw inverse/controlled access and source
`ctrl` obligations remain unsupported; failure does not select another profile.
The complete emitted artifact still requires fresh native validity and source
replay before execution. A provider outside its concrete
profile also rejects, rather than losing its Meaning request. Other static
constructors retain their explicit projection restrictions.
The rename changes no AST meaning, primitive, protocol/schema, checker or
constitutional edition; the later bounded implementation retains the existing
independent evidence gates.

## Bounded exact Meaning composition

A finite endomorphic Meaning declaration has one of these bodies:

```text
MeaningBody ::= permutation_by ( Identifier )
              | phase_by ( Identifier )
              | compose ( Identifier , Identifier )
              | tensor ( Identifier , Identifier )
```

`compose` and `tensor` are contextual identifiers in this position, not reserved
words. Operands resolve to declared Meanings through ordinary visibility rules;
forward references are allowed, while dependency cycles reject. Every declared
Meaning is checked, including unused declarations. A runtime value or classical
function name is not a Meaning operand.

If `First` and `Second` both have the exact basis tree `A`,
`meaning M: A = compose(First, Second);` applies First and then Second.
Writing their actions as
`First|x> = zeta_8^a[x] |p[x]>` and
`Second|y> = zeta_8^b[y] |q[y]>`, the result sends `x` to `q[p[x]]`
with phase `(a[x] + b[p[x]]) mod 8`. Composition requires identical trees;
equal physical dimension does not admit an implicit conversion.

If `Left` has basis `A` and `Right` has basis `B`,
`meaning T: (A, B) = tensor(Left, Right);` requires that exact ordered pair.
The first field occupies the low-order axes. For dimensions `dA` and `dB`,
column `x + dA*y` goes to `p[x] + dA*q[y]` with phase
`(a[x] + b[y]) mod 8`. Nested products and zero-width fields retain their type
identity; in particular a scalar phase on `Unit` is not discarded.

For example:

```qli
classical fn flip(b: Bit) -> Bit { not b }
classical fn z_phase(b: Bit) -> (Bit, (Bit, Bit)) { (0, (0, b)) }
meaning X: Bit = permutation_by(flip);
meaning Z: Bit = phase_by(z_phase);
meaning ZX: Bit = compose(Z, X);
meaning Ordered: (Bit, Bit) = tensor(Z, X);
```

These constructors normalize monomial targets within the existing six-bit
finite bound and work limits. Equality retains every column, exact phase and
axis order; it is not probability equality or equality up to global phase.
For example, `compose(X, Z)` differs from `ZX` by a minus sign. Target formation
does not prove a provider correct: `checked_op` and refined parameters still
require the existing fresh native comparison against the independently formed
request, with original source/dependency and provider identities retained.

The finite source route supports its existing closed observing entry. The
selected hierarchy route supports its existing pure input/output entry for
these refined operations; a readout entry outside its existing profile still
rejects. No readout/instrument rule is broadened by Meaning composition.
Rectangular arrows, nonmonomial/reference/instrument Meanings and general
matrix-versus-composite equality remain unfinished under
[#46](https://github.com/MGYamada/Qleisli/issues/46) and
[#83](https://github.com/MGYamada/Qleisli/issues/83). These bounded constructors
do not complete those Issues or establish source-to-request preservation.

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
