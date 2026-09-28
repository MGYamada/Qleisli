# B019 finite trusted-boundary audit

Date: 2026-09-28. Product: the 0.1.9 development tree. This is a completed
source-and-regression audit of the finite IR verifier, semantic-evidence
boundary, exact arithmetic, reference execution and current foreign adapters.
It supplies part of B019-3; the frontend/project/CLI audit, F2 repair and final
candidate reproduction are separate parts of the overall B019 disposition.
It does not by itself declare all six B019 gates complete.

The starting point was the [B019 assessment](b019-2026-09-28.md), the
[finite-rule inventory](../current-status.md#finite-rule-inventory), the
[finite IR argument](../finite-core-proof.md), the
[SC contract](../semantic-contracts-v0.1.md), the
[FC contract](../function-contracts-v0.1.md) and the
[M1.1 terminal profile](../interop-m1.1.md). The audit compared the actual safe
Rust entry points and every `RawOp` verifier/executor branch with those
contracts, rather than treating the inventory as an audit result.

## Reviewed boundaries and dispositions

Each row records an inspected obligation and its disposition. Test names refer
to actual regressions executed below. “Closed” means no unresolved violation
of the existing finite contract was found in this review; it is not a theorem
that arbitrary Rust execution is correct.

| Boundary and inspected implementation | Concrete check and evidence | Disposition |
| --- | --- | --- |
| Untrusted IR and checked handles: [IR](../../src/ir.rs), [`verify` and `verify_with_budget`](../../src/verify.rs) | `VerifiedProgram` has private fields and immutable raw access. Every public `RawOp` is matched by the verifier; its declared effect cannot authorize an unchecked operation. Failed checking returns no checked handle. Raw branch destruction is iterative, including rejected deep trees. | Closed. Public IR remains untrusted; no unchecked checked-handle constructor was found. |
| Ownership, wire freshness and complete exits: `State::consume`, `insert_token`, `Global::reserve_wire`, and final output checking in [verifier](../../src/verify.rs) | Tokens are checked for uniqueness and liveness before removal; wire IDs cannot be reallocated after retirement; complete output equality covers zero-width tokens. Executed `copied_quantum_token_is_rejected_even_for_unit`, `implicit_drop_is_rejected`, `wire_ids_are_never_reallocated_even_after_measurement` and the large-live-set regression. | Closed. `Unit` has no axes but still has a linear owner. Mutation before returning an error is confined to the discarded local verification state. |
| Classical scopes and complete branch transport: `verify_branch`, `Global` scope methods in [verifier](../../src/verify.rs), `relabel_branch` in [simulator](../../src/sim.rs) | Both arms start with the same live context, but share global freshness history. Phis cover every live owner exactly once with matching widths. Classical phi inputs are checked simultaneously before any phi output is installed. Executed undefined/inactive scope, cross-arm freshness, incomplete/mismatched phi and same-merge classical-read rejection cases. | Closed. Renaming transports axes; it does not combine quantum amplitudes from different measurement histories. |
| Gates, lifts, control and phase: `check_table`, `check_circuit`, `check_unitary_steps` in [verifier](../../src/verify.rs) | All lift columns are present, in range and injective where required. Circuit control/action axes are disjoint and in range; monomial phases lie in `0..8`. Same-width injective lifts are unitary; growing lifts raise the effect. Scalar phases survive empty target lists and legacy qif arms. Executed verifier, exact-contract and simulator phase/layout cases. | Closed. Equality of dimensions alone never supplies unitarity. |
| Restricted cleanup: `verify_compute` in [verifier](../../src/verify.rs), `Extraction::computed` in [independent extractor](../../src/contract/function.rs), `run_protected_use` in [simulator](../../src/sim.rs) | A total predicate feeds the same computed relation; source and auxiliary basis labels are preserved by the permitted uses. Target owners are distinct, auxiliary IDs fresh, and all target/control indices checked. Executed noninjective-predicate acceptance, H/X protected-use rejection, target-gate and controlled scalar-phase comparisons. | Closed for the published raw and source subsets. The raw-only target/protected-use vocabulary remains compatibility debt, not a newly adopted source feature. |
| Certified cleanup: `check_computed_inner` in [contract checker](../../src/contract/mod.rs), `CertifiedCompute` in [verifier](../../src/verify.rs) and [simulator](../../src/sim.rs) | Bound circuits are validated before cloning. Every row of `W E_f = E_f u` is compared exactly, including leakage rows. Fresh auxiliary construction supplies entry; ownership is separately checked. Executed wrong predicate/meaning/phase/leakage, zero-width ownership, shared-budget and actual auxiliary execution regressions. | Closed. Numerical cleanup alarms cannot issue release evidence; no standalone release primitive exists. |
| Exact scalar and matrix arithmetic: [exact kernel](../../src/contract/exact.rs) | Private canonical dyadics distinguish the four ring coefficients; checked integer arithmetic rejects overflow. Matrix constructors validate nonzero dimensions before products/indexing. Isometry checks include cross-column inner products. Shared budgets precharge bounded matrix operations. All ten exact-kernel unit tests passed, including denominator/sign extremes and exhaustion. | Closed for the declared ring, dimensions and arithmetic capacities. Alternate evaluation orders may fit when the selected order exhausts capacity; the documented rejection is not approximation. |
| Encodings and compositional evidence: `Encoding`, `Contract`, `CheckedContract` in [contract checker](../../src/contract/mod.rs) | Constructors require isometries and exact basis-tree/dimension agreement. Sequential composition matches complete middle encodings; tensor retains low-axis order; adjoint requires square logical isometry; control requires identical entry/exit encoding. Binding compares complete circuit/contract values. Executed all 20 semantic-contract regressions. | Closed. `check_entry` checks theorem-interface compatibility, not possession of a runtime state in the encoded subspace; this distinction is explicit in SC-3 and the public API contract. |
| Function evidence and immutable dependencies: `FunctionEvidence::check`, `preflight`, `inspect_steps`, `Extraction`, `check_binding` in [function evidence](../../src/contract/function.rs) | Both raw functions are independently verified after bounded preflight. Extraction follows complete output axes, both raw branches are checked, and equality includes phase. Private receipts keep source/raw snapshots and proof identities; dependent evidence has bounded depth/expansion. Executed all 19 function-evidence tests, including stale bindings, reversed joins, inactive invalid arms and shared-DAG bounds. | Closed. A cloned receipt preserves its issued identity; a separately checked receipt is a new dependency. Source metadata identifies compiler input but does not prove frontend meaning preservation. |
| Mathematical targets and retained application: [meaning adapter](../../src/contract/meaning.rs), `Circuit::matrix` in [contract checker](../../src/contract/mod.rs) | Meaning constructors validate whole permutation/phase tables and exact type trees; canonical target IR is checked through existing receipts. Retained calls validate axis count, placement and nonoverlapping controls. Three target regressions and the new 4,608-case audit sweep below passed. | Closed. No target name, source digest or author identity can issue evidence. |
| Observation instruments and numerical execution: `project_remove`, `execute_op`, `execute_ops`, `run_closed` in [simulator](../../src/sim.rs) | Measurement consumes its owner, reset begins a fresh zero wire, and hidden outcomes remain separate unnormalized ensemble components. Public outcome aggregation sums probabilities. Closedness, qubit/component/retained-amplitude/step limits are distinct checks. Executed Bell measurement/feedback/reset/discard cases and six source/IR correspondence regressions, including reference statistics. | Closed within the documented approximate reference profile. Tiny nonzero probabilities, underflow and floating error are not exact semantic evidence or hardware results. |
| Legacy execution adapter: [private adapter](../../src/ir/compat.rs), `run_qif_arm` in [simulator](../../src/sim.rs) | Legacy qif steps enter the common numerical circuit executor with the outer control and phase retained. Its steps are precharged once; the independent exact extractor does not call this adapter. `legacy_qif_matches_independent_exact_extraction_and_retains_limits` passed. | Closed. Numerical code sharing does not remove any trusted verifier acceptance rule. |
| Foreign input and export: [OpenQASM parser](../../src/interop/openqasm.rs), [terminal profile](../../src/interop/profile.rs), [QIR writer](../../src/interop/qir.rs), [public entry points](../../src/interop/mod.rs) | Checked bounded tokens/integers, explicit reset prefix, exact gate definitions, fresh owner reconstruction, terminal measurement/result order and hidden outcomes. Imports always call `verify`; exports accept verified closed IR and independently reject unsupported operations/capacities. All nine adapter tests and independent exact columns for all twelve gates passed. | Closed for M1.1-A. QIR input, adaptive profiles, arbitrary angles, device execution and general translation proofs are unimplemented future capabilities. External parser/LLVM execution is a separate final-candidate gate, not claimed by this local adapter test run. |

The [producer/debt inventory](../interoperability-roadmap.md#ir-reduction-and-the-trusted-boundary)
matches the inspected code: source qif uses `ApplyUnitary`; raw `QuantumIf`
remains accepted for compatibility; restricted source computation emits a
proper subset of the raw `ProtectedUse` vocabulary; terminal import adds no
checker constructor. Removing those public variants requires a versioned
migration. Their continued, specified acceptance is not an unresolved current
soundness defect or a reason to claim that the trusted core has already shrunk.

## Executed regression evidence

On macOS arm64 with Rust 1.98.1, the following command completed successfully
against the working tree on 2026-09-28:

```sh
cargo test --offline --target-dir target/b019-audit --lib \
  --test verify --test sim --test semantic_contracts \
  --test function_evidence --test meaning_evidence \
  --test source_ir_correspondence --test interop
```

It passed **118 tests**: 19 library, 29 verifier, 13 simulator, 20 semantic
contract, 19 function evidence, three meaning evidence, six source/IR
correspondence and nine interoperability tests. This includes the private
numeric/exact differential and physical-auxiliary execution checks. The
counts describe this execution, not a future candidate's total test count.

The new [audit regression](../../tests/b019_trusted_boundary.rs) independently
enumerates all 24 permutations of two bits and eight phase-offset patterns.
For each of those 192 actions, it checks all six ordered placements in a
three-bit register, both control values and forward/adjoint application through
retained function evidence: **4,608 exact operator comparisons**, covering all
64 entries of each resulting matrix. The oracle computes the basis map and
input-indexed inverse phase directly without the implementation's remapping or
inversion helpers. Inactive control blocks retain identity; active blocks
retain the scalar phase. This finite sweep is not a general algebra proof.

```sh
cargo test --offline --target-dir target/b019-audit --test b019_trusted_boundary
```

Result: **one test passed**, all 4,608 cases. No production fix was needed for
these audited core paths. The overall candidate must rerun its primary/MSRV
and final distribution checks after all cooperating changes have landed.
`cargo clippy --offline --target-dir target/b019-audit --test
b019_trusted_boundary -- -D warnings` also passed.

## Independent review of the F2 source-retention repair

The later F2 change was reviewed separately after the initial boundary sweep.
The reviewed paths are `RetainedIdentity`, `validate_identity`,
`FunctionEvidence::check_retained_diagnostic` and `check_binding` in
[function evidence](../../src/contract/function.rs), `MeaningEvidence::check_retained`
in the [meaning adapter](../../src/contract/meaning.rs), `Compiler::retained_sources`
in [compiler state](../../src/frontend/compile/mod.rs), and the
[provider](../../src/frontend/compile/operations.rs) and
[apply-contract](../../src/frontend/compile/lower/function_contract.rs) consumers.

**Disposition: compatible repair accepted by this independent review.** The
public owned `FunctionIdentity` fields, public checking signatures and
`identity() -> &FunctionIdentity` remain unchanged. The new storage is private:
receipts share a frozen `Arc` source snapshot, and an explicit call to
`identity()` lazily creates one bounded legacy owned view for that receipt.
Clones of the receipt share this view. Ordinary checking, equality, debugging,
binding checks and execution do not force a source copy per receipt.

The storage handle is not a certificate. Both owned and shared identities
pass the same metadata validation; raw preflight, independent verification,
exact extraction and full operator equality are unchanged. Per-receipt exact
checking still charges its metadata against its own evidence budget.
`check_binding` compares complete names and source bytes without materializing
the legacy view. Source mutation or a changed dependency cannot update an
already issued receipt. Public callers cannot access or mutate the private
shared storage. The thread-safe immutable handle and lazy view require no
new supported Rust version.

The compiler charges and copies the complete loaded source snapshot once,
retaining comments, unrelated modules and bundled standard source. This removes
the unintended multiplication of that storage charge by provider/contract-pair
count. Existing specialization, source metadata, raw representation and exact
checking limits remain independently enforced. The public metadata inspection
cost is explicit; this repair does not promise unlimited source or receipts.

After the repair, the same command above was rerun with
`--test b019_trusted_boundary --test source_snapshots` added. **All 126 tests
passed**, including 23 library tests, the new exact sweep and three
[source-retention integrations](../../tests/source_snapshots.rs). The latter
check 256 providers in 100 KB of main source plus 25 KB of unrelated comments,
256 distinct contract pairs and mixed consumers, rejection of specialization
257, retained exact source views, stale dependency/name/path/byte rejection,
and receipt lifetime after the original project changes or disappears. The
four new internal tests additionally check one-time charging, shared storage,
lazy compatibility views and unchanged metadata/budget/raw/equality rejection.

## Proof and assumption ledger

The [formal ledger](../formal-core.md#4-theorem-status-and-proof-work) and
[Lean ledger](../lean-resource-proof.md) accurately separate:

- Resource/scope projections and local Kraus/semantic-equation lemmas proved
  in Lean, with their explicit premises.
- Conditional paper proofs for source rules, transformations and ideal IR
  instruments.
- The unproved correspondence between actual Rust acceptance/extraction/
  lowering and those mathematical models.
- The separate approximate numerical executor, algorithm correctness and
  hardware assumptions.

The pinned environment remains Lean/Mathlib 4.30.0. [Audit.lean](../../lean/Audit.lean)
collects transitive axioms of every root-imported project declaration and
permits only `propext`, `Classical.choice` and `Quot.sound`; proof holes,
native-evaluation axioms and project-specific axioms fail. The production
[root](../../lean/Qleisli.lean) imports the resource, scope, transition, phi,
examples, Kraus and semantic-contract modules. The documentation checker
separately checks root coverage. No Lean source or theorem was added by this
audit.

`lake env lean -DwarningAsError=true Audit.lean`, run from `lean/` during
this audit, passed for **577 project declarations** and reported only the
three allowed axioms. This reruns the project audit against the existing
pinned build; the final candidate's complete Lean build remains recorded in
the combined validation report.

The [preserved Physlib audit](../physlib-environment.md) is explicitly historical:
eight external declarations were checked in the former dependency environment.
Physlib is not currently imported or required. Reintroducing it requires a
concrete instrument bridge, compatible pinned dependencies and a new scoped
external audit; its old success cannot certify the future bridge.

A whole-compiler proof, arbitrary-reference denotation mechanization and Rust
arithmetic/extractor correctness remain open research obligations. B019-4
requires their honest ledger and retained axiom audits, not their completion.
This inspection and the executed finite tests do not upgrade any of those
claims to proved.
