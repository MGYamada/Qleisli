# Changelog

Versions follow the [versioning and compatibility policy](docs/versioning.md).
Development milestones and the scope of their evidence are recorded
separately in [release milestones](docs/release-milestones.md).

## Unreleased

## 0.2.1 — 2026-09-30

Release selected for the first crates.io upload as `qleisli`; actual publication
and validation are recorded in the [release record](docs/releases/v0.2.1.md).

- **Rust package/import migration:** adopt `qleisli` for the first crates.io
  release at the user's explicit request. Earlier Git/path users must rename
  the `qleisli-core` dependency and `qleisli_core` imports, or use the documented
  Cargo alias. This is a narrow pre-registry identity exception; CLI/source/IR
  semantics remain unchanged. Registry publication is authorized after rechecking.

- Prepare the first crates.io release: add a registry README,
  checkout-independent quickstart, Rust API example/guide and discovery metadata.
  Repair rustdoc formatting and require warning-free docs plus doctests in CI.
  Extend clean distribution validation to install the extracted package and run
  documented source, bundled-library and ownership checks outside the checkout.
  Document package contents and the separately authorized publication step.

- Adopt Resource Safety as the third theorem pillar toward v1, alongside
  Soundness and Physical Realizability. Record the 2026-09-30 trust-boundary
  amendment as **to prove**: finite static resource bounds, compositional cost
  semantics and preservation through actual compilation. Add RS-C1–C5 without
  claiming existing ownership/work limits prove them or changing 0.2.1/0.2.2 gates.

- Add a structured `qleisli interop` CLI and installable Python host package
  for finite import/check/run/sample/export. Optional pinned PyQIR reads the
  declared QIR 2.0 Base text/bitcode subset before Rust ownership/IR checking;
  retain exact gate meanings, terminal measurement and explicit output order.
  Adaptive input and all-in-one platform wheels remain outside this slice.
- Split the release at the completed corpus/review/experimental-component
  boundary. Retain bounded connections in 0.2.1; move heavy measured shared-QPE
  implementation, production integration and proofs to 0.2.2 with unmet gates.
  The original corpus completion goal is deferred, not achieved.

- Reuse the same coherent QPE source in local order-finding and finite
  amplitude-estimation clients. Add explicit natural/operation forwarding in
  declaration order, preserve capability checks and key instantiations by
  complete nested providers. Small-system phase/reference and sign-fault tests
  pass; measured `CBits`, classical-result and production integration remain open.

- Add shared sized AddK and Equals sources with coherent carry, recursive
  controls and input restoration. Extend the experimental producer with explicit
  multi-owner calls/control/adjoint and complete-content imported-graph sharing.
  Validate widths 0–3, inverse/controlled clients, empty ownership and seven
  arithmetic faults; use small-system source regressions in CI. Production
  integration, named arithmetic binding and efficient general synthesis remain open.

- Add one shared coherent QPE source with explicit controlled access, bounded
  static powers, a reusable Hadamard definition and the same imported inverse
  QFT. Validate small selected sizes, reference states, off-grid phases and
  phase-sensitive provider changes. Follow the user's small-system validation
  scope for remaining work, preserving the earlier (8,8) limit as history;
  measured `CBits`, named QPE binding and production integration remain open.

- Add shared sized QFT source with explicit output reversal, dyadic phases and
  guarded affine sizes. Connect ordinary source modules and `adjoint` to the
  same shared graph; independently check forward Fourier requests and inverse,
  repeated-call and entangled-frame behavior. Record actual repeated execution
  cost; production CLI, QPE/CBits and general source preservation remain open.

- Prioritize actual corpus source: add one sized Xor and one sized GHZ
  definition with an untrusted development compiler and independent native
  reconstruction at every selected width. Check complete basis columns,
  coherent reference columns, linear/size failures and valid-but-wrong circuit
  mutations. Production sized-source CLI integration remains open.

- Connect singleton Fourier requests to the existing fresh `check_against` API.
  Compose complete Lean artifact checking with actual Fourier inspection;
  reconstruct all finite proofs and every phase-fixed H from the same bytes.
  Enforce the named contract's closed single-`Bits<n>` boundary and retain the
  full request, aggregate budgets and conditional unitary/reference proofs.
  Production hierarchy values and native/reader correspondence remain open.

- Bind the actual complete QFT entry to an independently requested Fourier width
  and interface. Derive identity renaming, recursive coefficients and explicit
  output reversal from actual bodies; prove full complex/reference amplitudes
  under bound exact-H obligations. Native widths 1–8 fit the unchanged shared
  budget. Production transport/seals, correspondence and source/corpus gates
  remain open; external schemas stay disabled.

- Compute phase-free wiring from actual shared hierarchical definitions and
  prove exact physical coefficients with arbitrary reference amplitudes.
  Check the QFT producer's outer renames/SWAPs within the existing aggregate
  budget; retain whole-artifact typing and the separate full Fourier-root gate.

- Classify proof maintenance by importance and retirement intent. Extend the
  temporary-proof inventory to the legacy reference alias and transitional
  QFT/QPE projection interfaces, with explicit replacement/removal gates.
  Retain actual-checker proofs, reusable mathematics and all current audits.

- Bind the complete shared recursive QFT body through one structural budget.
  Prove its full reversed-output Fourier coefficients from actual base,
  control/repetition and recursive definitions, leaving only bound exact finite
  H equations and transitional reader/native assumptions. Fresh H reconstruction
  rejects X, global -H and stale owner bindings. Complete actual outer reversal,
  independently requested Fourier roots and source/corpus integration remain open.

- Prove the shared QFT stage coefficient law and the explicit output-reversal
  equation, retaining full phases and reference amplitudes. Bind actual
  five-node stage geometry with a bounded pure inspector and native mutation
  checks; exact H, recursive/base and complete requested-root obligations remain
  explicit, with all external schemas still disabled.

- Clarify that GitHub Issues require no duplicate local backlog entry, update
  or backlog ID; retain existing backlog history.

- Bind actual shared-gradient definitions through a bounded Lean inspector and
  prove their complete complex diagonal by induction, including empty owners,
  actual routing and arbitrary reference amplitudes. Native producer/mutation
  checks and independent phase probes fit the existing shared budget. Complete
  outer QFT/Fourier and source/corpus integration remain pending.

- Prove exact diagonal laws for the actual hierarchical complex operators,
  including controlled repetitions, tensor products, inverse routing and
  arbitrary reference amplitudes. Add sparse coefficient scaling/control
  helpers with kernel proofs and independent native checks, without expanding
  repeated bodies. Complete QFT graph/Fourier binding remains pending.

- Reuse the actual complete-artifact typing context in conditional ordinary
  rule matching, with Lean proofs of the original acceptance predicate.
  Preserve all endpoint/phase/premise checks and existing work ceilings.
  Directly lifted QFT hierarchy fixtures pass through width four. A subsequent
  shared-gradient producer retains recursive register boundaries and shares
  controlled repetitions, admitting every width 1–8 without new checker rules
  or larger budgets. Independent Fourier schema/source integration remains open.

- Bind the supported conditional hierarchy to a separately supplied root
  contract through the actual Lean checker and fresh exact Rust reconstruction.
  Prove equal requested denotations and unitary/reference laws under the actual
  finite obligations. Preserve sharing and phase; reject coordinated circuit/
  meaning mutations, malformed pair proposals and aggregate work excess.
  Add a compatible request API and CI checks; complete production/profile,
  sized-source and corpus integration remain pending.

- Reaffirm the required Lean backend and its ban on `unsafe def`,
  `@[implemented_by]`, `@[extern]` and `partial def`. Extend existing source/
  compiled-audit CI regressions to nested backend modules, private/generated
  helpers and axiom-free theorems with runtime replacements. This changes no
  production acceptance rule and does not implement the future backend.

- Adopt sequential Rust-to-Lean pipeline migration from either end, retaining
  independent IR checking at the language boundary and extending the verified
  downstream segment through actual-pass preservation proofs or translation
  validation. Keep external candidate search, including rotation-synthesis
  norm-equation search, behind a planned proved Lean `LeafRealizer` checker;
  apply the de Bruijn criterion per pass without requiring all code to migrate.
  Keep the fixed trust partition and existing authority/proof gates.

- Plan Qleisli type-system specification as part of the v0.3.0 breaking-change
  release and defer QLT implementation to v0.4.0 or later. Concrete type rules
  and migrations remain to be specified; current 0.2.1 contracts and manifests
  are unchanged by this scheduling decision.

- Connect strict hierarchy JSON to a fresh native Lean conditional check and
  reconstruct every returned finite obligation from the same immutable bytes
  under one shared exact budget. Retain sharing under zero and large powers;
  reject phase/type/binding faults and malformed transport. Keep independent
  root-contract acceptance, remaining profile rules and external schemas pending.

- Propagate bound finite-leaf unitarity through actual conditional derivations,
  constructing a common unitary entry and both inverse laws with arbitrary
  finite references. Add strict exact matrix byte transport with independent
  dyadic exponents and fresh reconstruction of both sides of a finite equation.
  Keep all existing capacities and the explicit Rust/decoder correspondence
  boundary; complete hierarchy transport and production acceptance remain open.

- Compose actual finite reconstruction obligations through a separate bounded
  hierarchical derivation pass, retaining every request even under zero powers.
  Prove constructed operator and reference-map equality conditional on exact
  interpretations of those leaf bytes. Keep host/decoder correspondence
  and production acceptance pending.

- Add a finite unitary-leaf adapter that reconstructs complete QIRF1/2 bytes,
  checks exact type/owner/axis boundaries and an independently supplied matrix,
  and shares the existing exact-work budget across leaves. Preserve scalar phase
  and zero-width ownership. Add a pure Lean projection with proved binding of
  actual finite requests to indexed bytes, interfaces and encodings. Connecting
  those requests to the Rust result and the remaining leaf
  profile is still pending.

- Add an untrusted shared-call expansion into existing rewire/sequence nodes,
  preserving the actual callee index. Prove its coordinate transport and
  unitary/reference laws; check generated artifacts with independent phase
  and axis mutations. Retain the measured fragmented-header capacity case.
  Production call transport and sized-source integration remain pending.

- Adopt linear size obligations and explicit ordered bit-segment reshape in
  the 0.2.1 design, with `n+1` recursive interfaces and checked size transport.
  Preserve the first `n+m`/`2*n` source and real parser failure. Add focused
  axiom guards for the two existing reshape theorems; sized source, the new
  arithmetic/segment proofs and the separate array API remain pending.

- Begin the authorized sized-corpus continuation with preserved Xor source and
  actual diagnostics. Prove whole-space unitarity laws for the existing
  hierarchical complex operators, including coherent control and arbitrary
  finite reference extensions; bind phase, rewire and structural leaves to
  actual typing predicates. Recursively derive entry unitarity from supported
  internal checker success without assumed child isometries. Finite leaves,
  remaining full-profile rules and sized source remain pending. Correct the
  remaining current-design `CWord` table entry to `CBits`.

- Address the [0.2.0 review](docs/reviews/v0.2.0.md): prevent roundoff drift from
  rejecting long samples; count shared source snapshots once in QIRF and reuse
  imported storage; remove empty error locations; list all CLI commands/options;
  reject Lean `#eval`/`#eval!` in runtime source policy. Clarify numerical residues,
  improve finite-capacity diagnostics, and add `check_reference_value` while
  preserving the narrower `check_reference` compatibility theorem.

- Adopt the standard-library goal of a BLAS/LAPACK-like foundation for quantum
  computing integrated with a textbook and formal specifications: readers
  should be able to learn quantum information by reading the library. The
  comprehensive organization and generalized APIs remain separate decisions.

- Add a proved experimental canonical-reshape metadata helper before sized
  source: explicit single-owner regrouping preserves typed leaves, ordered
  axes, labels and reference coefficients without basis enumeration. Keep
  desired source, counterexamples and independent native checks; no new
  production rule or `reshape` source API is enabled.

- Expand the approved three-source input corpus from 24 to 30 finite translations:
  majority-oracle Deutsch–Jozsa, Bell measurement, constant addition, equality,
  LCU projector embedding and quantum-kernel overlap. Preserve first attempts,
  pinned originals and source-specific notices; add phase/reference oracles
  and six deliberate type-correct semantic faults. No new language rule or
  general algorithm support is claimed.

- Select development version 0.2.1, synchronizing Rust and both Lean packages
  with the [continuation record](docs/releases/v0.2.1.md). Shared sized QPE,
  production hierarchy and H1–H5 remain pending under the existing plan.
- Fix the README soundness formula for GitHub rendering by replacing
  `\operatorname` and specialized double-bracket macros with basic TeX notation.

## 0.2.0 — 2026-09-29

Finite machine interfaces, sampling and trials, arity-preserving tuples,
resource-policy review fixes and the experimental Lean kernel/proof foundation.
See the [migration and validation record](docs/releases/v0.2.0.md) and
[GitHub publication evidence](https://github.com/MGYamada/Qleisli/releases/tag/v0.2.0).
Production finite verification remains Rust-authoritative; common sized QPE
and the remaining production hierarchy/H1–H5 work target 0.2.1.

- Record a future 0.x.0 Lean-assisted mathematical debugger: bounded obligation
  reports, independently checked mismatch witnesses and IR/source/backend
  tracing, distinct from missing evidence or undecided checks. No debugger is
  implemented and no current release or theorem gate is added.

- Split the release scope: retain implemented finite interfaces, tuple/resource
  policy changes and the experimental Lean foundation in 0.2.0, with migration and
  release validation recorded separately. Move remaining production hierarchy,
  sized source/shared QPE and execution/H1–H5 to the 0.2.1 target without
  weakening their gates or permitting incompatible PATCH changes.

- Construct successful, unique complex denotations from actual supported
  hierarchical derivations, removing the assumed interpretation environment
  for their entry operator/reference equations. Keep whole-space unitarity,
  finite reconstruction and full source/schema integration as separate gates.
  Mark known migration-only proofs `temporary` with replacements and removal
  conditions; maintain their normal build, audit and API compatibility checks.

- Bind the three closed component schemas to rebuilt Lean theorem types,
  parameter domains and a content revision of their source/audit dependencies.
  Add CI and source-archive manifest checks; external schema entries remain
  disabled until full IR/provider binding is implemented. Add bounded scheduling
  for the full hierarchy's dependency graph, prove actual-checker acyclicity,
  and test shared graphs and aggregate capacities without semantic expansion.

- Record the fixed architectural trust partition in [TRUST_BOUNDARY.md](TRUST_BOUNDARY.md):
  trusted foundations/specifications, soundness/realizability proof obligations,
  and independent validation of untrusted frontend output.

- Record the future QLT mathematical test-language design, first source drafts
  and semantic counterexamples. Plan a Rust exact/cost/doctest experiment in
  0.3–0.4, followed by instrument evaluation, Lean migration and later interval
  certificates. No QLT runtime is implemented and no 0.2.0/S05/PR gate is added.

- Adopt the Physical Realizability Theorem and a proved Lean backend as v1
  requirements: derive CPTP semantics from soundness, then construct and
  synthesize its isometric dilation over a declared gate set. Clarify the
  longer-term Lean migration beyond the frontend and the remaining boundaries
  of an end-to-end guarantee. This records a plan, not a completed proof.

- Prove the actual QPE controlled-power schedule and residual target/reference
  instrument, with fresh-zero, measurement-order and retained-owner checks.
  Prove all-outcome completeness and joint trace preservation under an explicit
  provider-isometry premise. Derive both inverse laws for the accepted QFT
  graph and denotation existence from QPE acceptance. Add native width/mutation tests and independent
  off-grid coherence, normalization and missing-outcome counterexamples.
  Fixed component dispatch now binds theorem IDs, versions, independent
  parameters and actual witnesses, with semantic acceptance theorems. Full
  external IR/provider/registry binding remains pending.

- Bind the QFT theorem to an internal typed shared-circuit graph: exact
  `Bits(m)` interfaces, effects, call boundaries, actual dependencies and final
  data permutation. Prove cached checking agrees with literal graph execution
  and extend the Fourier/reference theorem to that graph's coefficients. Add
  native semantic mutations, graph limits and sharing-cost checks; external
  hierarchy projection and schema registry remain pending.

- Prove symbolic H/phase path compilation and the actual width-1–8 QFT
  circuit matcher's positive normalized Fourier coefficients, including final
  reversal and arbitrary reference amplitudes. Add native symbolic and independent
  Fourier comparisons, a type-correct wrong-reversal source, CI and retained
  proof attempts. External schema/typed hierarchy binding remains pending.

- Prove local Hadamard cancellation and phase normalization for arbitrary joint
  amplitudes in the Mathlib-free runtime. Add a one-way complex interpretation
  bridge in the separate proof package, including local probability identities
  and the existing phase/layout checker's weighted basis transitions. Validate
  the actual native normalizer with independent complex oracles and two retained
  source clients. This adds no external acceptance profile or QFT/QPE schema.

- Connect sparse dyadic phases to typed shared layouts in the experimental Lean
  kernel, including controlled conditions and retained scalar phase. Prove actual
  normalization/remapping/composition and request binding, charge claim validation
  and preserve expanded phase counts after cancellation. Add independent native
  and finite-source interference tests, pure API limits, CI and retained records.
  Non-diagonal gates, general transforms and QFT/QPE schemas remain pending.

- Connect typed layouts to shared calls and ordered composition in the experimental
  Lean kernel. Compute actual dependency/adapter maps once per definition, bind
  every receipt and the separate request, and prove acceptance against direct
  graph semantics. Add native mutation/scaling oracles, pure-API limits and CI
  coverage; retain first source, proof/audit diagnostics and validation records.
  Production QPE hierarchy and source integration remain pending.

- Continue CD-3 with a Mathlib-free typed layout checker: exact n-ary type trees,
  complete owner/axis permutations including zero-width owners, independent
  requests and proved inverse/reference reindexing. Add native rejection and
  16-bit capacity tests. General hierarchy integration and QPE remain pending.

- Preserve tuple arity and nesting across source AST, type checking, ownership
  and finite evidence: `(Bit,Bit,Bit)` differs from `((Bit,Bit),Bit)`.
  Add the consolidated [type contract](docs/type-system.md), explicit conversion
  and [migration rules](docs/tuple-shapes.md), and source/external-evidence
  regressions. Existing binary interfaces retain their shapes. This supersedes
  the earlier plan to preserve the 0.1.8 left-folding rule.
- Adopt Rust as the default when type or ownership design is uncertain;
  document quantum-specific differences and their checking obligations.

- Begin CD-3 with a Mathlib-free shared phase DAG checker: explicit owner ports,
  exact shape tags, independently bound summaries and requests, closed powers
  without body expansion, and actual cyclic-action soundness proofs. Add native
  mutation/scaling CI and preserved first-source diagnostics. Full hierarchical
  QPE, complex interpretation and sized source remain pending.

- Make proof of the **Qleisli Soundness Theorem** the central v0.5.0 milestone,
  with explicit production-kernel scope and S05-C1–C5 gates. Plan broader
  community open-source development from v0.5 onward, with preparation in
  0.4.x and translation validation from 0.6.0. These are future targets, not
  completed proofs, a license change or a current-version bump.

- Adopt the [staged Lean kernel migration](docs/lean-kernel-migration.md). Add a
  Mathlib-free Lean 4.30.0 executable phase-word checker with an actual
  acceptance soundness theorem, independent requirement protocol, Rust launcher,
  compiled-declaration audit and native differential CI. Production Rust
  verification and the pending common-QPE/H1–H5 gates remain in place.
  Development Python checks now require Python 3.11 for standard-library TOML.

- Retain shared sized QPE/QFT as the 0.2.1 continuation target and R14/H1–H5;
  name copyable measured sequences `CBits<m>`.
- Add trajectory sampling, the seeded `sample` command and typed fresh-trial
  host APIs, including bounded validated period/factor postprocessing.
- Apply bounded CLI source loading with explicit capacity/legacy overrides;
  preserve legacy Rust loader/compiler entry points. This default is breaking.
- Implement bounded QIRF1/QIRF2 transport and independent contract requests,
  exclusive atomic `emit-ir` and fresh-process `verify-ir`. Reconstruct finite
  evidence through the existing exact checker and retain complete root types.
- Preserve first QPE/Grover attempts and real baseline diagnostics. Hierarchy,
  external schema binding and sized source are still pending; component proofs
  are included in the experimental Lean foundation.
- Address the [v0.1.9 follow-up review](docs/reviews/v0.1.9-followup.md): share
  exact work across compilation, use repeated squaring, compare finite closed
  transforms independently, and reject bare CR throughout source. Aggregate
  checking capacities and the CR restriction are breaking 0.2.0 changes.
  Extend corpus link checking, consolidate helpers, harden source opening on
  macOS/listed Linux targets and hash-pin the external validation wheels.


## 0.1.9 — 2026-09-28

Compatible review fixes, the completed finite B019 foundation and preparation
for code-driven development. See the [release record](docs/releases/v0.1.9.md)
and [GitHub publication evidence](https://github.com/MGYamada/Qleisli/releases/tag/v0.1.9).

### Added

- A closed three-source [input corpus](corpus/README.md): 24 finite executable
  translations from QuantumKatas, Qualtran Bloqs and PennyLane Demos, pinned
  originals/licenses/hashes, per-case contracts and exclusions, initial authoring
  snapshots and real diagnostics. Independent numerical oracles check 9,412
  semantic probes, with four local rejection fixtures. No upstream framework
  or general algorithm implementation is claimed.
- Adopted [source/licensing policy](corpus/POLICY.md): preserve MIT for Katas
  translations and Apache-2.0 for the other two; Qleisli stays Apache-2.0.
  Source additions/replacements require an explicit policy amendment.
- Explicit [development method](docs/design-philosophy.md#start-with-the-quantum-programs-we-want-to-write):
  start with quantum programs as they ought to be expressed, then develop the
  language with AI. Record current-source friction as A020-14–16 without
  adopting syntax, new checker rules or continuous-angle APIs.
- A dated [B019 boundary check](docs/reviews/b019-2026-09-28.md), with a local F2
  reproduction, finite revalidation and explicit audit/candidate closure work.
  Preserve it as the initial assessment; subsequent closure has separate records.
- Completed [B019 finite foundation](docs/reviews/b019-completion.md), with
  frontend/trusted-boundary review dispositions, an independent 4,608-case exact
  phase/layout/control/adjoint sweep, successful exact-commit Linux CI and clean
  package/complete-source-archive checks. Publication remains separate.
- A [code-driven continuation procedure](docs/code-driven-development.md), with
  source-grounded obstacles A020-17–20 and bounded work packets for the
  user-selected 0.2.0 direction. It adopts no future grammar or checker rule.
- A clean-commit distribution checker for the verified production package and
  complete source archive, including nested research, proofs, exact source bytes
  and third-party notices; CI also checks its adversarial regressions.

### Fixed

- Reject incomplete or invalid M1 `StaticOp` syntax at the current token/EOF
  before consuming a constructor. Previously `g[` could panic (exit 101),
  violating the existing grammar error and X1 single-JSON failure contracts;
  it now returns `expected a static operation description`, `parse`, exit 1.
  Keep EOF as a parser sentinel. Regressions cover all constructor/example/std
  token prefixes, exact spans, JSON `check/run` and Markdown `doc` failure.
- Make CI whitespace checking compare the entire committed tree with the empty
  tree, so a clean checkout no longer turns the check into an empty comparison.
- Share a single bounded immutable source snapshot across static-provider and
  function-contract receipts, charging source bytes once before copying.
  [F2/A020-10](docs/reviews/b019-f2-resolution.md) is resolved without changing
  public owned identities, source/raw binding, exact checks or existing limits.
  The 100 KB/256-provider case and an additional 25 KB comment module now pass.

### Changed

- Locate function-effect failures at a causal expression and show derived and
  declared effects, retaining declared callee effects and both-branch checking.
- Suggest checked separate imports and ordinary unary wrappers for unsupported
  grouped imports and static `h/x/z/t` arguments. Explain retained source copies
  when a new provider/contract snapshot exhausts the existing work budget.
- Clarify direct versus constructor-derived capabilities and record source
  snapshot accounting omitted from the original M1 work-unit description.
  Preserve current accepted derivations and limits; A020-09 remains future
  opaque-provider design work, while A020-10 is resolved by shared retention.
- Distinguish ideal iterative-QPE probability one from floating-point residuals.
  Record additional authoring feedback and pending multi-error/boilerplate/display
  work as A020-11–13, without a model benchmark or new syntax claim.

No public Rust/IR/evidence API, accepted source meaning, JSON v1 schema,
dependency or toolchain requirement changes. No capacity is reduced; duplicate
snapshot work is removed. The 0.1.8 migrations remain historical.

## 0.1.8 — 2026-09-28

Fixed-width operation contracts and executable authoring improvements, with
version **0.1.8** retained at the user's request. See the
[implementation/migration record](docs/releases/v0.1.8.md) and
[GitHub publication evidence](https://github.com/MGYamada/Qleisli/releases/tag/v0.1.8).
Historical entries retain the version policy used at the time; the revised
policy below governs new changes.

### Added

- Fixed three-bit iterative QPE in ordinary `.qli`, compared with coherent QPE
  and an independent Fourier-instrument oracle on off-grid entangled inputs.
- Preserved first-source and curated repair sessions, with actual diagnostics,
  revision snapshots and CI checks for record integrity.

- A living v0.2.0 issue backlog connecting authoring friction to concrete
  source evidence, acceptance experiments and existing checking dependencies.

- Basis function parameter patterns for product components, whole subtrees
  and ignored basis values, checked through existing finite tables.
- N-ary tuple types, values and patterns, left-folded to exact binary trees.
  Independently checked pair meanings, executable clients and negative
  ownership/shape/depth regressions exercise these forms.

- Runnable Bell/teleportation/dense-coding/swapping components and shared
  operation-parameter QPE, amplitude-amplification and Hadamard-test examples.
  A checked-in `.qli` corpus covers successful clients, rejected authoring
  attempts and type-correct algorithm faults, including reference correlations.
- A concise implemented-source reference whose complete code fences compile
  and execute in Rust CI, and an evidence-based authoring feedback report.
- Fixed-width static operation parameters, explicit access constraints and
  bracket arguments, phase-fixed permutation/phase meanings, `bind_op`, and
  six checked composition constructors. One unchanged client can accept
  independently checked implementations of the same meaning.
- `FiniteMeaning` / `MeaningEvidence` reuse existing monomial and function
  evidence. Final IR retains receipts; no core acceptance rule is added.
- Parametric access/type/ownership checking and concrete exact cleanup checks,
  bounded specialization, source/evidence rejection regressions and a runnable
  operation-contract example.

### Changed

- Include expected/actual exact types in concrete mismatch diagnostics and
  suggest the explicit logical-contract form for restricted cleanup failures;
  keep acceptance, source locations, error categories and JSON v1 unchanged.

- Replace public Rust `Param.name` with `Param.pattern`; this incompatible
  AST migration is documented while the user retains development version
  0.1.8. Existing accepted binary `.qli` programs retain their meaning.
- Locate unreturned quantum ownership at its actual binding, including
  nested patterns, shadowing, parameters and computed-region binders.

- Align initial-development versioning with Cargo: for 0.y.z with y > 0,
  compatible fixes/features/syntax additions use PATCH; breaking changes use
  MINOR. Compatible features need no exception. Preserve historical migrations
  and the 0.1.8 checkpoint; 1.0+ rules and verification gates are unchanged.
- Reserve the new M1 keywords and extend public AST/token/error records;
  follow the release record's source and Rust migration. JSON v1 gains emitted
  `capability` / `contract` cases within its specified category set.
- Render meaning definitions and access requirements in source documentation.
- Split parser routines to preserve existing deep-syntax acceptance/rejection
  without increasing stack requirements. Keep old IR, toolchains and limits.

QIR import, remaining machine interfaces, type/size generalization and M2 remain
separate work. The [v0.2.0 backlog](docs/v0.2.0-backlog.md) includes reconsidering
the tuple layout itself; 0.1.8 retains explicit binary trees and left-folded sugar.

## 0.1.7 — 2026-09-28

Start M1 with JSON results and bounded OpenQASM 3/QIR connections, under the
user's explicit feature-release exception. This is new functionality, not
compatible-maintenance-only work. The [release record](docs/releases/v0.1.7.md)
and [GitHub publication evidence](https://github.com/MGYamada/Qleisli/releases/tag/v0.1.7)
separate implementation, validation and publication.

### Added

- Start M1.1-A with bounded OpenQASM 3 import/export and QIR 2.0 Base text output.
  Require explicit OpenQASM initialization, retain exact gate phases and output
  order, and independently verify imported ownership through the existing core.
  Add a Rust host example, adversarial/exact tests and independent parser/LLVM
  validation. See the [connection contract](docs/interop-m1.1.md).
- Start M1 X1 with opt-in `--format=json` for `check` and `run`: one version-1
  `qleisli.result` object on stdout, including failures, stable categories,
  nullable original-source locations, and lexicographically ordered distributions.
- Add structured frontend diagnostic APIs alongside the unchanged legacy error
  APIs. Preserve parser/load provenance and coordinates from the loaded source
  snapshot, including Unicode, CRLF and empty EOF spans.
- Validate JSON independently with Python's JSON decoder as well as Rust CLI
  golden and diagnostic regressions; run the JSON suite in primary/MSRV CI.

### Changed

- Adopt the project title “Qleisli: A Language for Structured Quantum Algorithms”
  and the tagline “Write quantum algorithms in the language you use to think
  about them.” in a shorter README with a runnable introduction.
- Translate AGENTS.md into English, preserving the working rules and explicit
  version exceptions. Retain historical Japanese validation records, bilingual
  glossary terms and legacy link anchors.

### Compatibility and scope

- Human output and existing successful invocations remain unchanged. Unknown,
  duplicate or missing-value flags are usage errors. Prefix a path starting with
  `-` by `./`. `doc` keeps its existing Markdown interface and rejects JSON mode.
- JSON mode requires UTF-8 path identities. Non-UTF-8 paths report `project`
  without an invented location; legacy human mode retains its path support.
- Clamp only JSON probability endpoint roundoff within 2^-40; reject nonfinite
  or materially out-of-range output as `numerical`. The numerical reference
  simulator and exact evidence checker are unchanged.
- No new `.qli` form, core checking rule, IR variant, production dependency, existing capacity or
  toolchain requirement. New adapters have explicit local bounds; validation-only
  OpenQASM/ANTLR and LLVM dependencies run separately. QIR import, adaptive
  connections and Python distribution remain pending. X2–X6, N1–N6 and M2 remain unimplemented.

## 0.1.6 — 2026-09-28

IR/evidence maintenance plus the user's explicit version-policy exception for
the comment/docstring extension. Rust and Lean project versions remain at
0.1.6. The [implementation and validation record](docs/releases/v0.1.6.md)
separates local checks from exact-commit CI, tagging and publication in the
[GitHub release record](https://github.com/MGYamada/Qleisli/releases/tag/v0.1.6).

### Documentation feature and migration

- Add nested `/* ... */` comments and Rust-style `//!`, `///`, `/*! ... */`
  and `/** ... */` documentation. Check attachment, retain original byte spans
  and expose metadata separately through `parse_documented_module`; existing
  public AST fields and lexer token variants stay unchanged.
- Add `qleisli doc <source-file>` and Markdown rendering without execution or
  a verification claim. Document every bundled module and all twelve public /
  three private definitions in English; ordinary stdlib checking is unchanged.
- Doc spellings previously treated as arbitrary comments now require valid
  placement. Line comments end at LF/EOF; bare CR is forbidden in doc text.
  Use ordinary comment spellings or LF/CRLF when migrating, as described in
  the [extension specification](docs/documentation-comments.md).
- Keep 0.1.6 at the user's explicit request despite the normal MINOR rule.
  This feature and its source-acceptance changes are not compatible-only
  maintenance; the exception does not apply to future feature work.

### Fixed

- Enforce the existing raw-IR limit of 64 nested classical branches before
  entering either arm. Previously a 65th branch with empty arms was accepted;
  it now receives the existing depth-limit diagnostic at that branch.

### Validation

- Add raw-IR cases at 63, 64 and 65 levels, with empty/nonempty deepest arms
  on both sides, checking acceptance and rejection locations.
- Check function-evidence preflight at 31, 32 and 33 levels in both the
  implementation and specification, including inactive empty branches and
  complete zero-width ownership. Its existing 32-level bound is unchanged.

### Design

- Select future Python bindings and bounded OpenQASM 3/QIR import/export to
  reduce adoption cost through a shared checked compiler core. Record phase,
  ownership, measurement-reuse, evidence-binding and wheel-installation gates.
  This is a [direction](docs/interoperability-roadmap.md), not implemented
  interoperability or a completed extension specification; features require MINOR.
- Adopt the small trusted-core boundary: convenience belongs in untrusted
  desugaring, not in the checker. Inventory raw-only IR variants as compatibility
  debt and specify the obligations for a future versioned core reduction.
- Define desugaring consistently as meaning-preserving translation to already
  specified core operations with untrusted output for independent checks.
  Distinguish it from source checking, runtime adaptation and approximation.
- Record the risk of fixing the design to one future gate architecture and the
  recommendation to parameterize coefficient domains, separating exact,
  approximation and device/noise contracts. Cite STAR primary work; keep the
  current R8 implementation and selected M2 angle profile unchanged.

### Internal

- Route legacy raw `QuantumIf` arm execution through the existing finite
  `CircuitStep` vocabulary. Preserve public IR, independent exact extraction,
  in-place primitive execution and existing execution-step limits. This removes
  duplicate numeric interpretation, not verifier rules or evidence obligations.
- Compare all legacy arm primitives, both polarities, empty/Unit arms and mixed
  sequences with independent exact extraction, including coherent references,
  reversed physical axes, exact budget boundaries and state-vector reuse.

The IR/evidence changes preserve existing valid core programs and public IR.
The comment extension adds APIs and the documented lexical/attachment changes
above. Quantum rules, declared capacities, dependencies and toolchains are
unchanged; no original M1/M2 slice or general proof is implemented.

## 0.1.5 — 2026-09-27

Compatible review/design maintenance release. Rust and Lean versions are
synchronized at 0.1.5. The [release record](docs/releases/v0.1.5.md) separates
local validation from the exact commit, CI, tagging and publication recorded
in the [GitHub release](https://github.com/MGYamada/Qleisli/releases/tag/v0.1.5).

### Changed

- Reflect the [v0.1.4 review](docs/reviews/v0.1.4.md) with a concrete next-scope
  dossier and version-independent M0–M5 milestones. Fixed-width M1 may retain
  existing finite checking; bounded kernel continuation and hierarchical IR
  gate M2 size generalization. Replace indefinite deferral and no-go completion
  with a selected path and dated scope checkpoint.
- Advance the local v0.1.5 maintenance roadmap with explicit completion
  evidence for review/specifications, checks and distribution; keep exact-commit
  CI, tagging and publication as pending release gates.
- Complete the selected future M1 language and machine-interface specifications:
  static grammar/access judgments, permutation/phase meanings, portable finite
  IR/evidence, JSON diagnostics, trajectory sampling, typed retries and source
  limits with legacy migration. Specify the bounded M2 hierarchy/schema/QPE
  profile and implementation acceptance matrices; no new feature is implemented.
- Correct the follow-up specification review: retain and independently validate
  exact root input/output type trees in portable IR, reject equal-width tree
  substitutions in requested contracts, and define controlled operations in
  the existing least-significant-control basis order. Add future acceptance
  cases; these interfaces remain unimplemented.
- Make truth-table-free reversible synthesis and hierarchical IR/evidence
  binding explicit scaling prerequisites. Record basis-derived semantic
  vocabulary, ideal dyadic QPE angles, early portable evidence/JSON/sampling
  slices and special-form/public-IR migration as future MINOR work.
- Prioritize independent IR-verifier and evidence-kernel proof obligations;
  select finite instrument/CPTP semantics as the first planned Physlib use.
- Defer Physlib to that future concrete bridge: remove its direct requirement
  and five exclusive transitive packages, drop its default CI build/audit,
  and preserve the external probe under research. Retain all nine Mathlib
  dependency records, Lean/Mathlib 4.30.0 and Qleisli proof declarations.
- Centralize mutable planning state and a fourteen-group rule-to-code,
  test and proof inventory in JSON; generate Markdown and reject drift in the
  existing document checker. Preserve historical records and legacy IDs.
- Correct AE's conjugation-based access/cost account, Shor indentation and
  dependency-history wording; simplify AGENTS.md to durable rules and links.

### Validation

Add five document-checker regressions and six phase-sensitive conjugation
convention fixtures. The [validation record](docs/releases/v0.1.5.md#local-validation)
states actual local checks and remaining publication gates. Numerical fixtures
do not establish general theorems or execute imaginary source.

No production/research Rust, Qleisli proof declaration, public behavior,
supported capacity or toolchain change. The unused external Lean dependency
is removed as above; no `.qli` migration is needed. Experiments importing
QuantumInfo directly must declare their own Physlib dependency.

## 0.1.4 — 2026-09-27

Compatible documentation/plan maintenance release. Rust and Lean project
versions are synchronized at 0.1.4. The [release record](docs/releases/v0.1.4.md)
records validation scope; the [GitHub release](https://github.com/MGYamada/Qleisli/releases/tag/v0.1.4)
identifies the exact commit, CI, tag and published source distribution.

### Changed

- Adopt the [v0.x plan](docs/v0x-roadmap.md) and B019-1–B019-6 boundary through
  v0.1.9: finite-core compatibility and conformance, evidence-boundary review,
  explicit proof obligations, next-minor decisions and reproducible validation.
- Make operation capabilities the next design focus alongside ownership,
  effects, established auxiliary invariants and proof contracts. Require new
  abstractions to remove an author obligation through independently checked
  evidence. Existing finite effects and certificates remain the foundation.
- Assign conditional themes from v0.2 toward v1 without adopting new syntax
  or APIs. Preserve the symbolic-kernel deferral with no selected release,
  the scaling prerequisite, six imaginary drafts and executable V1-C1–C5.
- Align current-version guidance and remove the stale README statement that
  the preceding 0.1.3 release was still awaiting publication.

No production/research Rust or Lean source, public contract, supported capacity,
toolchain requirement or dependency changes. The independent non-published
research package retains 0.1.3. No migration is needed.

### Validation

Fresh local candidate checks pass on macOS with Rust 1.98.1 and 1.85.0:
258 production and 43 research tests each, primary fmt and all-target Clippy
for both packages. Pinned Lean builds and separate audits pass for 577 Qleisli
and eight Physlib declarations. All 43 Python tests, 52 mathematical checks,
39 exact assertions and all ten CLI projects and Shor pass. The
[P014 record](docs/releases/v0.1.4.md#local-candidate-validation) separates
candidate distribution checks, clean-commit CI and publication. These results
do not complete later maintenance audits or new language features.

## 0.1.3 — 2026-09-27

Compatible maintenance and mathematical-research release. The Rust and Lean
packages remain aligned at 0.1.3. The [release record](docs/releases/v0.1.3.md)
states validation scope; the [GitHub release](https://github.com/MGYamada/Qleisli/releases/tag/v0.1.3)
identifies the exact commit, CI, tag and published source distribution.

### Fixed

- Reject empty, ragged and dimensionally incompatible matrices in the
  imaginary-design and exact semantic-contract helpers before `zip` can
  silently truncate data. Preserve valid rectangular/scalar fixtures and
  rational/quadratic arithmetic.
- Reject NaN and infinity in either comparison operand, including complex
  components, with `ValueError`. Invalid input cannot make positive or
  negative mathematical checks pass. Finite comparison tolerance is unchanged.
- Add 29 helper regression tests across the two suites and run both in CI.
  Preserve the existing 52 imaginary-design checks and 39 exact assertions.

### Design and independent research

- Verify the supplied v0.1.2 review against the tag and release CI. Require
  composition without whole logical dense matrices before size generalization,
  with an explicit first-QPE angle and exact/approximate checking profile.
- Record a first-principles meaning/implementation/evidence architecture and
  an independent, non-published symbolic semantic-kernel prototype. Its typed
  terms, frozen requested contracts and bounded exact leaves support a limited
  raw-IR adapter; it does not change production source acceptance or execution.
- Add 20 local Lean semantic lemmas with explicit premises. These mathematical
  rule proofs do not prove correctness of the Rust checker or compiler.
- Retain the prototype and regressions while deferring further kernel development
  and production integration to future roadmap work, with no target release.
- Record isolated Physlib/QuantumInfo and lean-quantum interface experiments,
  with pinned sources, reproducible probes and declaration-level axiom evidence.

### Lean environment

- Add Physlib's compatible `v4.30.0` commit
  `f5242c99d796b59a390d26cd7d1a8057e04c46b5`, preserving Lean/Mathlib 4.30.0
  and all pre-existing dependency revisions. Lock the inherited documentation
  dependencies and record their licenses.
- Build selected QuantumInfo state/channel/measurement dependencies in CI and
  audit eight external declarations separately from all Qleisli declarations.
  Library availability does not establish source/IR semantic correspondence.

### Validation and compatibility

Local macOS release checks pass on Rust 1.98.1 and minimum Rust 1.85.0:
258 production tests and 43 research tests each, primary fmt, and Clippy on both.
The 43 research tests include 5,425 exact differential cases within one test.
Python checks cover 18 imaginary-helper, 11 exact-helper and 14 document-checker
regressions, plus the 52 mathematical checks and 39 exact assertions.
The release record separates local checks, hosted Linux CI, package validation
and publication evidence.

Production Rust behavior, existing public contracts, capacity limits and
supported toolchains are unchanged. No source migration is needed.
Imaginary source and production symbolic integration remain unimplemented;
these checks do not establish general compiler soundness.

## 0.1.2 — 2026-09-27

Documentation/design maintenance release. Both project manifests are
synchronized at 0.1.2. The [release notes](docs/releases/v0.1.2.md) record scope
and validation; the [GitHub release record](https://github.com/MGYamada/Qleisli/releases/tag/v0.1.2)
identifies the tagged commit, required CI, source archives, and publication.

### Changed

- Align current-version records and define a staged roadmap for six imaginary
  Qleisli 1.0 algorithm drafts, per-draft semantic contracts, a shared
  requirements index, semantic review, and release validation.
- Make the next-minor sequence explicit: complete the existing imaginary-v1
  prerequisite, select and specify the smallest required generalization,
  then implement and validate it with evidence retained in final IR.
  V1-C1–C5 remain the separate executable acceptance target.
- Translate ten current Japanese design, planning, overview, and finite-IR
  proof documents into English. Preserve semantic premises, proposal/proof
  status, historical evidence, source links, and legacy heading anchors.
  Add a documentation authority/inventory map; retain Japanese operational
  guidance and original dated conformance entries as supporting records.
- Correct the review summary's odd-QSVT direction to right-to-left singular
  spaces, matching the unchanged `L p(Sigma) V†` contract and circuit.

### Added

- An English language-evolution framework separating current normative rules,
  imaginary notation, extension specifications, implementation and proof.
  Correct stale v0.1 status summaries without changing acceptance rules.
- Six original imaginary-v1 algorithm bodies for QPE, Grover, amplitude
  estimation, Shor, a symmetric Szegedy walk and QSVT; per-draft contracts,
  shared requirements R01–R14 and a semantic/counterexample review.
- A reproducible 52-check mathematical script covering Fourier/phase conventions,
  residual/reference coherence, amplification signs, factor validation, walk
  reflections, and QSVT parity/selector boundaries, also run in documentation CI.

### Validation and limits

Before English consolidation, the local 0.1.2 candidate passed 258 Rust tests and Clippy on both Rust 1.98.1
and 1.85.0, Lean build and its 527-declaration axiom audit, 14 documentation
checker tests, 39 exact examples, 52 new mathematical checks, all ten CLI
projects and Shor, and 155-file source-candidate packaging/rebuild. Linux CI
and clean-release-commit packaging are publication gates; their final results
belong in the GitHub release record. Subsequent
English translation passed independent fidelity review, document checks and
14 checker tests, the 39/52 mathematical fixtures, and updated 156-file
packaging/rebuild, recorded [separately](docs/releases/v0.1.2.md#english-documentation-consolidation).
It does not claim to rerun Rust execution tests, Clippy, or Lean suites.

The initial design-corpus prerequisite before 0.2.0 is met by the recorded
artifacts and review. All imaginary source remains uncompiled; no new language
forms, standard APIs or general proof guarantees are delivered. The
[release record](docs/releases/v0.1.2.md) and
[conformance ledger](docs/specification-status.md) distinguish local candidate
validation from clean-commit CI, tagging and publication. The compiler fixes
and historical results of 0.1.1 remain recorded under 0.1.1.

## 0.1.1 — 2026-09-27

Compatible maintenance release. Both project manifests are synchronized at
0.1.1. See the [release notes](docs/releases/v0.1.1.md) for scope and checks;
the [GitHub release record](https://github.com/MGYamada/Qleisli/releases/tag/v0.1.1)
identifies the published commit and its CI evidence.

### Changed

- Require an initial imaginary Qleisli 1.0 code corpus before v0.2.0 feature
  implementation or release, covering QPE, Grover, amplitude estimation,
  Shor, quantum walk, and QSVT. Noncompiling, revisable design code and its
  semantic requirements are distinct from executable v1 acceptance evidence.
  The policy is adopted; the corpus is still pending and is not a prerequisite
  for this compatible maintenance release.

### Fixed

- Reuse immutable function evidence within one frozen compiler project without
  repeatedly comparing and charging its source/raw snapshots. New artifacts
  still pay for snapshot copies; external binding checks remain exact.
- Point independent IR contract errors at the originating source expression,
  including nested branches, and report an exact counterexample entry.
  Parser messages identify parse failures without changing public error codes.
- Detect material numerical leakage before certified auxiliary projection,
  preserving exact release certification and unnormalized probability weights.
  Scale only the diagnostic ratio to prevent subnormal or underflowed weights
  from hiding leakage; preserve stored amplitudes and non-finite-weight alarms.
- Harden signed dyadic scaling against a future denominator-bound change and
  make contract-composition basis invariants explicit.
- Clarify CLI bit order and tiny numerical weights; address the reported
  older-Clippy expression/lifetime patterns and add Clippy to the MSRV CI job.
  Actual Rust 1.85 validation also identified test bit-packing expressions;
  explicit parentheses preserve their meaning and satisfy MSRV Clippy.

### Verification

- Validate the 0.1.1 candidate on macOS: 258 tests and all-target Clippy pass
  on both Rust 1.98.1 and minimum Rust 1.85.0. Documentation checks, 39 exact
  assertions, Lean build and the 527-declaration axiom audit, all ten CLI
  projects, Shor, and candidate source packaging/verification pass. Linux CI
  and clean-release-commit packaging are separate publication gates, recorded
  against the exact release commit in the GitHub release record.
- Reproduce the cleanup alarm's underflow failure before fixing it. Add a
  scale-invariance regression covering real/imaginary leakage, both sides of
  the alarm threshold, subnormal and zero-rounded weights, the smallest
  positive amplitude, and unchanged projected amplitude bits.
- Add deterministic generated comparisons of exact circuit matrices with
  numerical execution, adjoints, controls, and retained physical auxiliary
  implementations. See the [review disposition](docs/reviews/claude-v0.1.0.md)
  for checked findings, deferred design changes, and validation results.

## 0.1.0 — 2026-09-27

Initial source release. See the [release notes](docs/releases/v0.1.0.md)
for usage, verification scope, and known limits. The annotated `v0.1.0` tag
identifies the release commit; the GitHub release records publication.

### Added

- Finite `.qli` parsing, module resolution, type/effect/linear-ownership
  checking, independent raw-IR verification, and reference execution.
- Bundled finite basis, algorithm-routine, transform, and arithmetic
  definitions, with executable quantum-algorithm examples.
- Exact finite semantic contracts `U E_in = E_out u`, compositional evidence,
  and independently checked auxiliary zero return.
- `apply_contract` with immutable function evidence retained through
  composition, axis remapping, adjoint, coherent control, and repetition;
  interchangeable phase-oracle implementations under one fixed client.
- Explicit ownership, semantics, and source/IR specifications; a separate
  Lean development for the recorded ownership and matrix lemmas.
- Apache-2.0 licensing for Qleisli's own code, proofs, examples, and
  documentation, with contribution and versioning policies and explicit
  attribution to Masahiko G. Yamada.
- A Japanese design note on quantum bookkeeping as a language responsibility,
  with QPE, amplitude amplification, and Shor as successive design tests.
- CI coverage for the declared minimum Rust version, 1.85.0, alongside the
  primary Rust toolchain, Lean build/axiom audit, and documentation checks.

### Verification and limits

The [release validation record](docs/specification-status.md) reports the local
245 Rust tests, 14 documentation-checker tests, 39 exact mathematical example
assertions, Lean build and 527-declaration axiom audit, and package validation.
Those are implementation/model checks, not a general proof of the Rust compiler
or noisy-hardware behavior. General size/operation parameters, portable proof
loading, and the v1 algorithm-structure milestone remain open.
