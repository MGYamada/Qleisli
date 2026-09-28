# B019 frontend, authoring and command audit

Date: 2026-09-28. Scope: the 0.1.9 candidate's finite source acceptance,
lowering, standard source, host routines and CLI. This is the root review
complementing the independent [trusted-boundary audit](b019-trusted-audit.md).
It compares implementation paths with published rules and executed regressions;
inventory membership alone is not the evidence for the dispositions below.

“Closed” means that the review found no unresolved violation of the supported
finite contract after the recorded repairs. It is not a general Rust adequacy
proof or a claim to have enumerated all possible programs.

## Reviewed obligations

| Boundary and inspected code | Checks and disposition |
| --- | --- |
| [Lexer](../../src/frontend/lexer.rs), [parser](../../src/frontend/parser.rs), [AST](../../src/frontend/ast.rs) | Inspected every expression/static constructor, precedence, UTF-8 byte spans, forbidden characters, nested comments, EOF sentinel, depth and tree limits. F1 is repaired: constructor validation precedes token consumption, so incomplete static arguments return a located error. Prefix sweeps in [parser tests](../../tests/parser.rs) and [CLI JSON tests](../../tests/cli_json.rs) cover examples, bundled std and every static constructor. Public AST shapes and current left-fold tuple meaning are unchanged. Closed. |
| [Project loading](../../src/frontend/project.rs), [resolution and declaration checking](../../src/frontend/compile/mod.rs) | Canonical project roots, reserved std namespace, duplicate imports/declarations, visibility, symlinks below the root and import cycles are checked. All declarations, including unused ones, are checked in dependency order; cycle detection uses an explicit stack. [Project](../../tests/project.rs) and [source judgments](../../tests/source_judgments.rs) cover these rules. Source reading/tokenization are not governed by the later lowering budget; X6/A020-20 explicitly records the existing policy and future migration. Closed under the current policy, with no claim of an isolated unattended service. |
| [Types and basis functions](../../src/frontend/compile/basis.rs), [value trees](../../src/frontend/compile/lower/value.rs) | Checked exact product trees, zero-bit Unit ownership, parameter-pattern uniqueness, left-to-right basis order, total table evaluation and injective coherent lifts. Full finite domains, width/depth/node/work limits and output shape are checked before lowering a lift. [Compilation](../../tests/compile.rs) and [authoring ergonomics](../../tests/authoring_ergonomics.rs) cover partial/noninjective maps, tuple association and finite patterns. Closed. |
| [Lowering and effects](../../src/frontend/compile/lower/mod.rs), [lexical scopes](../../src/frontend/compile/lower/scope.rs) | Reviewed eager argument evaluation, declared callee effect joins, live/consumed binding identity, mixed classical/quantum moves, shadow lifetime, discarded expression results and function exits. Suspended call arguments remain in the complete register store. Causal effect metadata is private and cannot lower an effect or grant acceptance. [Source scopes](../../tests/source_scope.rs), [resource cases](../../tests/compile.rs), [source judgments](../../tests/source_judgments.rs) and [repair diagnostics](../../tests/repair_diagnostics.rs) pass; the scope model includes 7,225 finite identity transitions. Closed. |
| [Branch lowering](../../src/frontend/compile/lower/branch.rs) | Both arms are checked even for a constant condition; each starts from the same complete live environment and retains globally fresh IDs. Result owners and suspended frame owners are transported exactly once. Classical values merge only from valid branch scopes; pattern projection does not partially consume the caller on failure. [Branch/resource cases](../../tests/compile.rs), [scope](../../tests/source_scope.rs) and [source/IR reference tests](../../tests/source_ir_correspondence.rs) cover these paths. Closed. |
| [Sealed primitive lowering](../../src/frontend/compile/lower/primitives.rs) | Checked argument arity/types, distinct operand owners, split/join axis order, consuming measurement, fresh reset output and observing discard. Operations are independently verified after lowering; a sealed name or parser result is never a verified handle. [Standard-library source cases](../../tests/project.rs), [compile](../../tests/compile.rs) and [simulator tests](../../tests/sim.rs) cover the finite behavior. Closed. |
| [Static circuit extraction](../../src/frontend/compile/circuit.rs), [operation constructors](../../src/frontend/compile/operations.rs), [generic use](../../src/frontend/compile/lower/operations.rs) | Reviewed full output reindexing, phase-preserving adjoints, outer/inner control axes, tensor ordering, zero repetition, materialization bounds and exact meaning composition. Conjugation derives control using uncontrolled conjugators around the controlled middle action. Required access is checked before an empty repetition; named/spent local bindings cannot escape into the static namespace. Abstract generic checking cannot issue retained evidence; concrete instances are independently checked. F3 follows the published transparent-constructor contract and has phase-sensitive T/T† regressions in [operation parameters](../../tests/operation_parameters.rs). Opaque-provider tightening remains a future migration, not a current bug. Closed. |
| Restricted `with_computed` and [certified lowering](../../src/frontend/compile/lower/certified.rs) | Reviewed exact predicate domains, protected Z/T-only source use, isolation from outer quantum owners, joint data/auxiliary ordering and matching result owners. Certified bodies retain actual raw/circuit evidence; generic placeholders are discarded and checked concretely. The trusted checker independently establishes exact cleanup with all leakage rows. [Certified-source](../../tests/certified_source.rs), [static semantics](../../tests/static_semantics.rs) and [semantic contracts](../../tests/semantic_contracts.rs) cover acceptance and deliberate phase/leakage faults. Closed. |
| [Function-contract use](../../src/frontend/compile/lower/function_contract.rs), provider cache and private retained metadata | Reviewed exact interface matching, closed unitary dependencies, private frozen caches, full source/raw identity and the shared F2 retention path. No hash authorizes reuse. Public identity fields and methods are unchanged; the same evidence checker validates owned and shared metadata. [F2 resolution](b019-f2-resolution.md) records the removed duplicate cost, before-copy bounds, five unit checks and three [source regressions](../../tests/source_snapshots.rs), including changed transitive dependencies. Independently reviewed by the trusted-boundary reviewer. Closed after repair. |
| [Documentation attachment](../../src/frontend/documentation.rs), [diagnostic locations](../../src/frontend/diagnostic.rs), [command dispatch](../../src/bin/qleisli.rs), [JSON transport](../../src/bin/qleisli/json.rs) | Reviewed EOF attachment, ordered source spans, Unicode scalar line/column conversion, Markdown rendering, JSON escaping, one-envelope output and 0/1/2 exit distinctions. Generated docs issue no evidence. F1 and causal effect locations have text/JSON/doc regressions; grouped import and gate-wrapper suggestions compile in the repair suite. The public compile-error `0..0` sentinel remains documented representation debt, with no new invalid acceptance. Independent Python decoding checks transport separately from Rust JSON construction. Closed. |
| [Bundled ordinary source](../../stdlib/src), [public contracts](../stdlib-contracts.md), [host order recovery](../../src/host.rs) | Read every bundled `.qli` definition: Boolean totality, low-bit-first increment/add/multiply, signed reflection, parity instrument and QFT reversal/phase agree with their contracts. [Algorithm routines and QFT](../../tests/algorithms.rs), [order finding](../../tests/order_finding.rs) and the [source corpus](../../tests/qli_corpus.rs) provide finite independent comparisons. Host modular arithmetic uses bounded u32 inputs/u64 products; continued fractions validate the resulting order and nontrivial factor before returning success. Exhaustive Shor15 distributions do not claim actual random trials or general factoring. Closed. |
| [Input corpus](../../corpus/README.md), [authoring records](../../corpus/authoring/check-initial.json), [semantic oracle](../../scripts/check_input_corpus.py) | Source provenance is fixed to the three adopted corpora; licenses and frozen bytes are manifest-checked. Translations state finite restrictions. Twenty complete unitary matrices use control-sensitive X/Y interference; observation cases include branches and reference tomography. First attempts and failures remain intact. This is curated authoring evidence, not a model benchmark or proof of all upstream algorithms. Closed within the stated 24-case intake. |

## Findings and limits

F1 and F2 are resolved with compatible repairs and before/after regressions.
F3's currently accepted capability derivations are specified, rather than an
accidental bypass. F4 retains raw numerical output and clarifies roundoff;
optional presentation is A020-13. F5 now checks committed-tree whitespace.
F6's duplicate type conversion and diagnostic sentinel are explicitly retained
implementation debt, with no demonstrated violation requiring a new API.
No discovered supported-contract defect is deferred merely to close B019.

The [future obstacles](../code-driven-development.md) retain the real gaps:
sized source, hierarchical bound evidence, general predicate/arithmetic
synthesis, actual sampling/retry, portable IR and input-resource isolation.
They require their own specifications and experiments. General frontend
meaning preservation, Rust adequacy and numerical error bounds remain open
proof obligations in the existing ledgers.

## Executed validation

The final working-tree validation used separate fresh Cargo targets on
macOS aarch64, Rust 1.98.1 and the minimum Rust 1.85.0. On each toolchain,
all **354 production tests and 43 research tests** passed, as did all-target
Clippy with warnings denied. Primary formatting passed for both packages.
Independent JSON decoding passed seven tests with one Linux-only skip per
binary. These results include the repaired F2 paths, the independent 4,608-case
exact sweep and every integration suite linked above. The final committed
candidate, Linux CI and clean archive checks are recorded separately in the
[completion record](b019-completion.md); local passes alone do not discharge
that candidate gate.
