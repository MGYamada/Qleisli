# VM-27: native QIRF leaves, requests and H

The native slice checks original QIRF1/2 leaves, independent finite-request
equality and phase-fixed H for hierarchy roots, Fourier inspections, composed
instruments and named-QPE providers. It is not complete VM-27 closure.

`Protocol.HierarchicalFinite.checkPairs` reads both complete immutable matrix
descriptions under the existing canonical coefficient/dimension/work limits.
`Hierarchical.FiniteBinding.check` compares the actual matrices and proves that
success implies exact equality and the charged remaining budget. No Rust
matrix/equality flag or submitted success receipt is an input. The structural
checker still derives and binds the complete finite-pair obligation list.

`Qirf.checkGraph` derives edges from complete original raw operations, including
both classical arms, and checks the proposed order, reachability, cycles and
depth. Every program is freshly ownership/effect checked; every circuit or
meaning attachment is reconstructed with `Raw.BranchFunction.checkEntry`.
Original evidence IDs are retained, including non-topological tables. Meaning
targets generate canonical table circuits, never claimed extraction summaries.
`Qirf.check` binds exact legacy types, owners, ordered axes and output ports,
reconstructs the original root and requires full-space isometry and phase-exact
equality. Its equation theorem concerns the actual executable checker, not a
Rust result. H is reconstructed separately against the fixed mathematical
matrix; even a matching producer description for -H cannot redefine this role.

All five private pending modes now use version 3, with one native exact-work
budget of 10,000,000 across leaves, request pairs and H. Old replies reject
without fallback. `inspect_native`, `check_against_native`,
`check_instrument_native` and `check_qpe_instrument_native` retain immutable
inputs but invoke no Rust finite checker and create no executable leaf handle.
Existing public executable reports independently rebuild Rust sealed handles;
their separate equal-ceiling legacy work remains `exact_work`, while
`native_exact_work` reports native work. Rust-only finite paths are unchanged.

Tests exercise the native process directly with independently written packets:
both QIRF versions, phase, Unit, Toffoli, coherent branches, protected cleanup,
closed classical branches, invalid unselected arms, circuit/meaning dependency
graphs, false attachments, cycles, unused nodes, owner reuse, duplicate fields,
noncanonical numbers and trailing data. QPE tests coordinate changed QIRF and
description for X and -H and still require rejection. Existing host tests also
exercise native-only report APIs and reject malformed obligation transport.

## Semantics and decoder correspondence

[Qirf](../../../lean/Qleisli/Qirf.lean) proves actual `checkGraph` success
constructs an original-index graph from empty receipt slots. Full original
implementation/specification bodies, including both arms, have independent
`BodyMeaning`; every dependency slot is fresh and bound. Actual root
reconstruction binds the original program, type, owners, ordered axes and
final output, proves both complex inverse laws, and extends them to arbitrary
finite entangled references. It does not rely on basis probabilities.
[NativeHierarchy](../../../lean/Qleisli/NativeHierarchy.lean) discharges every
actual finite leaf into `LeafMeaning`, instantiates `Conditional.Derives`, binds
all independently derived finite pairs, and proves each phase-fixed H role
denotes its original body. These are actual-success theorems, not Rust-checker
or producer-receipt premises; the graph relation is proof plumbing over the
independent VM-26 body meaning, not a new acceptance-selected reference model.

The [decoder harness](../../../scripts/test_verification_decoders.py) compares
all fields of actual Lean decoded values against original QIRF1/2 JSON and
actual Rust QLH1 bridge bytes, including all 19 raw constructors, all 13
definitions/12 meanings/4 encodings/10 structural forms/12 enabled rules,
both branch arms, zero-repeat children, nontrivial ordered maps, nested types,
original evidence indices and exact embedded bytes. The test-only
[view](DecoderView.lean) is not a new public decoder or acceptance API.
The 362 cases include eight integer-range regressions found by this comparison:
QIRF step/control/evidence u32, function/permutation u16 and phase u8 bounds now
match the Rust wire fields. Semantic limits remain separate and unchanged.

The [whole-hierarchy comparison](../../../scripts/test_hierarchical_execution.py)
first uses native-only acceptance, then independently executes retained Rust
leaves against separate complex-coefficient oracles. Nineteen cases (four named
QPE), at most four combined qubits, compare 912 coefficients including phase,
all outcomes, unnormalized coherent inputs and entangled residual references.
Three fresh-shot clients additionally check 768 seeded outcomes. This is
independent test evidence, not a proof of Rust execution or arbitrary-size
analytic hierarchy semantics. CI includes both decoder and execution harnesses.

## Remaining gates

Rust sealed handles remain a compatibility dual gate, not a premise of native
finite checking. Complete root/Fourier/QPE analytic closure still needs the
budget-independent reader-to-`Operator` coordinate bridge that discharges the
existing constructed-evaluator leaf/H/provider premises. This slice does not
prove universal JSON/QIRF decoding, native compilation, source preservation,
Rust execution or schema binding. External schemas stay
disabled and production Rust authority is unchanged. VM-28 packaging/dual
integration, VM-29 coverage and S05 transfer gates remain open.

Routine [CI](../../../.github/ci/README.md) is test-oriented. Kernel proofs
remain in source and compile with the native checker; model proof maintenance
and full fresh proof/release validation are explicit separate lanes. Tests
are regression evidence, not a replacement for the established theorems.

The earlier request-only snapshot remains in [validation](validation.json).
Current checks are recorded in [native validation](native-validation.json)
and the full [native schema source/type audit](native-schema-registry-validation.json).
The later [semantic validation](semantic-validation.json),
[decoder validation](decoder-validation.json), [whole execution](semantics-validation.json)
and [semantic schema audit](semantic-schema-registry-validation.json) bind the
extension separately. [Before-fix decoder failures](decoder-before-bounds.json)
retain the actual eight rejected-domain decoding counterexamples.
