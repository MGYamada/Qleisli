# VM29 selected public paths and boundary migration

[Coverage](coverage.json) accounts for 36 VM22 groups, 20 public boundaries,
82 inventoried Rust source surfaces and 232 constructor variants. The checker
binds the reviewed APIs, constructors, capacities and non-Rust/CLI sources to
that inventory; changed surfaces or omitted/duplicate rows fail CI. Each row
names current component/production status, evidence and an explicit blocker.
[Decision #276](https://github.com/MGYamada/Qleisli/issues/276) supersedes the
earlier compatible-v0.2.9 scheduling decision: implement one Lean production
verifier in v0.2.9, while keeping full Soundness/review at v0.5.0. Migration is
complete for production acceptance implementation; release validation and proof
completion remain separate. The [cutover record](cutover/README.md) supersedes
the historical [first accepted-handle slice](native/README.md).

| Selected path | Actual implementation |
| --- | --- |
| Rust raw IR, QIRF versions/meaning entries/conversion | `native::Kernel::{verify,check_raw,check_program,check_with_meanings,convert}`; each accepted handle binds the native decision's original bytes. |
| Native-only QIRF inspection | `native::Kernel::inspect`; immutable bytes and native work, without constructing an execution view. |
| Source library/project/qrate | `check_project_with_kernel`, `compile_project_with_kernel`, corresponding `QrateSource` methods and CLI selection; all concrete bodies, including unused functions and expanded static-operation instances. |
| Foreign CLI/Python/QIR | All six interop actions and `Client(lean_kernel=...)`; QIR text/bitcode passes through the selected gate after translation. |
| Hierarchy/sized source | Native-only checking, execution and sampling of immutable actual artifacts; exact initialization-move binding retained. |

Untrusted serialization is separate from acceptance, with structural depth/node
bounds before recursion. Selected exports no longer perform a redundant legacy
import before their fresh native check. Sized execution no longer calls Rust's
finite-leaf IR verifier, matrix equation or isometry checker: the native checker
has already bound each actual body to the actual artifact's finite matrix.
Numerical execution only decodes those immutable descriptions and shares the
existing limits, axis conventions and RNG behavior. Public APIs exposing finite
leaf handles obtain fresh acceptance from the same native executable.

`ClassicalScope.ScopeSafe` independently specifies classical SSA/lexical scope.
`Raw.Observation.verify_scopeSafe` proves it for the executable checker, and
`Qleisli.NativeValidity.check_scopeSafe` composes it with actual immutable packet
acceptance, without a Rust decision or optional finite-request premise.
The proof covers both arms, global uniqueness after leaving scopes and phi
operands resolved before any destinations. Independent positive/negative
semantic examples accompany it. It is not full EffectSound/CPTP composition.

```sh
python3 scripts/check_verification_inventory.py
python3 scripts/test_check_production_coverage.py
python3 scripts/check_production_coverage.py
```

The [reviewed changes](boundary/source-review.json) bind changed source/API
surfaces and retained comparison tests. [Validation](boundary/README.md) records
performed checks and limitations for the earlier transitional state. No external schema is enabled.
The historical [small-client timing record](performance/README.md) compares release CLI
latency with and without selected Lean checking; it does not predict Lean-only
authority performance.
The historical [independent acceptance comparison](equivalence/README.md) ran
both verifiers on the same bytes, including invalid inputs and seeded mutations.
Those original bytes and decisions are retained for native-only replay.

`library/`, `project/` and `generic/` are curated small regression sources,
not upstream corpus additions or model-authoring benchmarks. The generic first
attempt and its real diagnostic are retained as `generic-first-attempt.qli.txt`
and `generic-first-diagnostic.json`; the executable fixture wraps the primitive
as required by the existing provider contract. The rejection harness targets
unused direct gates and instantiated retained calls, independently of `main`.

The following five S05 proof/review obligations remain open for v0.5.0.
Implementation removal now follows the separately adopted
[cutover criteria](https://github.com/MGYamada/Qleisli/issues/276);
passing those criteria does not close these obligations:

| Gate | Required result |
| --- | --- |
| S05-C1 | Every enabled rule/path/capacity and entry premise covered, with positive corpus coverage and compatible behavior or a reviewed migration. |
| S05-C2 | Composed soundness of actual acceptance over the entire declared profile, without a Rust acceptance premise. |
| S05-C3 | Reviewed theorem bound to released definitions; reproducible builds/audits/replay, Mathlib-free runtime and explicit execution assumptions. |
| S05-C4 | Independent requests and artifact binding; differential/adversarial/platform checks, with no fallback on kernel or transport failure. |
| S05-C5 | Published scope/reproduction, independent review resolving blockers, and contributor/maintenance/release/security procedures. |

Full ordinary-root EffectSound/CPTP and the native analytic-leaf-to-Operator
bridge remain genuine composition obligations. Existing finite Gram theorems
require a different checked computation and cannot be projected onto the
structural production verifier. Changing the implementation schedule or imposing an exponential replay
does not complete these proofs.

Source/backend preservation, native compilation, numerical execution and hardware
correctness remain separate proof duties; these gates do not silently add them
to the kernel soundness theorem. All five gates remain open. The record checker rejects a metadata-only claim that a
gate passed; closure needs actual proof/review artifacts and corresponding
checker changes. All accepted handles require a fresh Lean decision; no Rust
acceptance fallback remains. Planned general proofs are not replaced by finite tests.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
