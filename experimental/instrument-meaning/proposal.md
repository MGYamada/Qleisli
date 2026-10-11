# #46: bounded observing function contracts

**Status: ordinary language-design candidate, not adopted.** This packet
proposes one small extension to the existing `apply_contract` call. It changes
no constitutional interpretation, protected guarantee, edition or release
status. GitHub Issue #46 is the decision record. The experiment beside this
packet supplies observations, not acceptance authority.

## Decision requested

Adopt an observing overload of:

```qli
apply_contract(implementation, expected, input)
```

Both names identify closed ordinary functions with principal **Observe**
effects, one runtime quantum argument `Q<A>`, and exactly the same complete
result type. `input` is consumed once; the expression returns the implementation's
actual result with that type and effect. The expected function is a separately
selected specification, not executed as a second call on the live owner.

The first profile has no static parameters or runtime classical parameters.
Results may be finite tuples of ordinary `Unit`, `Bit`, `Bits<N>` and quantum
owners `Q<B>` already supported by the common source checker. The entire tuple
tree, zero-width owners, each quantum basis tree, ordered quantum ports and
ordered classical bit projection must agree. Equal widths do not establish
type equality. An unsupported result/lowering shape rejects explicitly.

This is a separate instrument contract family. It does not broaden the
Unitary-only `meaning M: A = reference(f)` constructor, `Meaning<A>` or
`Op<A,M>`, and grants no coherent control or adjoint access to an observing
function. General operation arrows and rectangular pure Meaning remain
deferred beyond v0.3.0. Ordinary function return arrows are unchanged.

## Accepted and rejected examples

The positive desired program is frozen at
`tests/fixtures/authoring_sessions/instrument-contract-v030/attempt-01/contract-readout/main.qli`:

```qli
observe fn readout_z(q: Q<Bit>) -> Bit { measure_z(q) }
observe fn implementation(q: Q<Bit>) -> Bit { measure_z(h(h(q))) }
pub observe fn main(q: Q<Bit>) -> Bit {
    apply_contract(implementation, readout_z, q)
}
```

The complete Z instrument agrees on all inputs, not only freshly prepared
zero. Inserting T immediately before destructive Z readout also preserves
this instrument: each resulting branch differs only by an unobservable
branch phase. In contrast, complementing the returned bit changes the public
outcome index and must reject.

The other frozen desired call compares nondestructive Z readout, which returns
the measured quantum state, with destructive readout followed by fresh zero.
Their outcome probabilities agree for every input. Their residual/reference
states differ, so the contract must reject. A pure operation with matrix `-I`
still differs from `I` under existing pure Meaning rules; instrument equality
does not relax that rule or permit coherent use of this overload.

All four initial CLI observations are retained. The existing observing control
checks; an observing target in pure `reference(f)` rejects its quantum result
type; both proposed contract calls currently reject the endomorphism-only
provider requirement. Those refusals validate no downstream instrument rule.

## Exact equality and independent semantics

For each public ordered classical result `y`, define the unnormalized map

```text
E_y(rho) = sum_h K_(y,h) rho K_(y,h)^dagger.
```

`h` ranges over all hidden measurement, reset and discard histories. No
postselection, branch normalization or sampled-output comparison is allowed.
The complete instrument must be trace preserving. Each map must agree with
the selected expected function on every input and every finite external
reference, including entangled inputs.

For the bounded finite profile, compare all exact Choi coefficients:

```text
J_y[(o,i),(o',i')] = sum_h K_(y,h)[o,i] conjugate(K_(y,h)[o',i']).
```

The row/column conventions use the actual ordered input and residual-output
ports. The public `y` follows the complete declared classical result tree.
Absent/impossible outcomes denote zero. Hidden labels, history order and
Kraus-list length are not semantic identifiers. Off-diagonal entries are
essential: equal outcome probabilities do not determine the residual channel.
The comparison is exact in the existing admitted scalar carrier. It introduces
neither a tolerance nor a new coefficient domain.

The mathematical CP-map definition must remain independent of the executable
checker. The implementation must prove the finite coefficient comparison's
soundness and its extension by an arbitrary finite reference. An experiment
that computes these coefficients in Python is not that proof.

## Native gate, identities and lowering

The designated Mathlib-free native Lean checker must reconstruct both complete
original program bodies, their selected roots and required dependency evidence.
The gate first checks the full compatible signatures, principal effects,
ownership, scope, and each complete instrument's trace preservation. It then
checks the exact outcome-indexed equation above. No producer-supplied matrix,
receipt, success bit or cached earlier acceptance can establish equality.

The evidence binds both original artifacts, ordered interfaces, required
meaning, source snapshots and dependencies. Swapping either root, dependency,
source snapshot, output order or implementation invalidates it. A separately
selected reference may intentionally be the same function, but that proves
only that selected equation, not adequacy for an unnamed external algorithm.

Both concrete adapters must preserve the common source obligation. Lowering
executes only the implementation and retains the checked pair and actual
instruction/owner/result boundary. Every source obligation must be discharged,
including unused closed declarations and zero-count children; unsupported
generic or erased boundaries reject rather than lose an obligation. Dependency
checking must remain fresh after substitution. Missing/incompatible checkers,
timeouts, malformed replies and exhausted limits reject without fallback.

The new native request variant and private paired evidence handle must not
change the existing QIRF representation or reinterpret old requests. Exact
protocol fields, version compatibility and rejection fixtures must be reviewed
before enabling the gate. Unsupported variants reject. CLI whole-root request
selection remains separate: checking this call does not set a request-free
root's `request_checked` or `source_meaning_verified` to true.

## Bounded profile and equality limits

Initial native reconstruction uses the existing dense six-bit input/output
component limit and shared work/transport limits. No limit is raised. Complete
histories and coefficient sums are charged to that budget; potentially large
cases reject at the limit rather than normalize, sample or trust a producer.
Tests use at most two live qubits and do not generate maximum-size cases.

Unsupported profiles and missing exact equality evidence are semantic
refusals, not guessed equivalence. This profile promises neither a symbolic
instrument calculus nor scalable all-width equality. Public composition here
is ordinary checked function composition; the complete resulting instrument
is checked. It does not add instrument `Meaning` constructors or first-class
observing operation values.

## Required verification and constitutional impact

Acceptance requires both adapters, exact result/owner mapping and independent
native evidence. Regressions must include redundant H H readout, branch phase,
public result relabeling/order, different hidden Kraus decompositions, unchanged
probabilities with a changed residual channel, entangled external references,
zero-width owners, unsupported signatures, false unused contracts, root/evidence
substitution, and checker/transport/budget failures. Existing pure phase and
control regressions must remain unchanged.

QS-2026-01 already requires complete unnormalized outcome-indexed maps with
arbitrary references. This proposal implements a bounded instance of that
adopted obligation. EXACT-2026-01 requires exact comparison; it supplies no
epsilon waiver. PR still requires correspondence of any admitted realization
with the actual emitted artifact; this function equation is not a target
realization theorem. Quantitative RS is not established by checker work limits.
Both admitted QLV1 ownership/scope guarantees and their current-evidence
continuity remain protected. No helper theorem enters the guarantee ledger
merely because it is proved.

Source lowering, native compilation/runtime, wire decoding and host execution
retain their actual proof gaps. Successful original-instrument comparison does
not prove the full source-preservation theorem or discharge QS, PR or RS as a
whole. No new binding interpretation, guarantee admission, QFT implementation,
release publication or completion of Issue #46 is requested by this adoption.

## Experiment evidence

`check.py` compares eight independently authored pairs, and additionally checks
hidden-history reordering, split Kraus decompositions and impossible outcomes.
The retained native experiment reconstructs all thirteen original programs;
their complete histories match the separate existing exact host oracle. Maximum
live width is two qubits. This establishes those observations only. Production
requested-instrument checking and its proofs have not been implemented.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
