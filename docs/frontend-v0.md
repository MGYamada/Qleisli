# Initial `.qli` frontend and verified IR pipeline

Status: **the minimum Stage 3–4 path is implemented and tested on finite cases**
(2026-09-26). This authoritative English implementation profile replaces the
previous Japanese edition. It describes name resolution, type/effect/linear
ownership checking, IR generation, independent verification, and reference
execution for [finite core v0](language-spec.md) and its [grammar](syntax-v0.md).
The explicit mathematical rules have paper soundness results; general Rust
adequacy, source-to-IR preservation, and external backends remain open.

Product 0.1.8 implements the [fixed-width operation supplement](next-minor-spec.md):
static parameters/arguments, independent access constraints, basis-derived
meanings and checked composition. Generic bodies are source-checked before
specialization; abstract checking produces no `VerifiedProgram` or cleanup
evidence. Each concrete expansion passes the existing independent checker.
The [release record](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/releases/v0.1.8.md) gives public AST/error and reserved-word
migration, executed validation and remaining gates.

The 0.1.8 authoring extension added product patterns to basis parameters.
The 0.2.0 [type specification](type-system.md) now retains n-ary tuple arity
and nesting, superseding the former left-folding sugar. See the
[grammar](syntax-v0.md#authoring-forms-added-in-product-018). Unreturned owners
now point to their actual parameter, local or computed-region binder, including
shadowed names; diagnostic codes/schema and ownership acceptance are unchanged.

<a id="入口と信頼境界"></a>

Concrete type mismatches now include expected/actual types in ordinary/basis
calls and returns, branches, static operation interfaces, primitives and
classical conditions/Boolean operands. Types print exact arity and nesting including
Unit factors. The restricted `with_computed` diagnostic points to the explicit
logical-contract form and its exact cleanup obligation. These are explanatory
message changes; categories, source locations, JSON v1 and acceptance remain
unchanged. [Repair regressions](../tests/repair_diagnostics.rs) cover both a
working correction and a false contract that still rejects.

From v0.2.3 every filesystem source tree declares Qleisli edition `"2026"` in
its closest enclosing `Qargo.toml`; missing or invalid declarations fail before
source parsing. The selected module root is unchanged. In-memory parsers use
the current 2026 grammar. See [language editions](language-editions.md) for
manifest discovery, the selected compatibility exception and migration.

## Entry points and trust boundary

The Rust APIs `frontend::compile::check_project(&Path)` and
`compile_project(&Path)` load a source root and check every declaration, including
unused functions. Bundled ordinary definitions in `std::basis`, `std::routines`,
`std::transforms`, and `std::arithmetic` receive the same checks.
`check_project` permits a library without `main`. `compile_project` requires
`observe fn main() -> T` in `main.qli`, with a classical result of the recursive
shape `T ::= Unit | CBit | (T1,...,Tk)`, k=2..64. Nested finite products
are permitted within the implementation limits; there is no two-leaf limit.

Each ordinary function is lowered from typed input resources and independently
IR verified. `compile_project` returns `VerifiedProgram`. These entry points
start from source files, rather than trusting public mutable AST or import
records supplied by a caller. Sealed names are resolved anew. The producer of
source or raw IR does not change its validation path.

The CLI provides `qleisli check <source-root>` and `qleisli run <source-root>`.
`run` executes a checked closed entry and prints result bits from left to right
with approximate probabilities. Unit leaves contribute no bits. These are host
commands, not new `.qli` forms or quantum operations.

The [documentation extension](documentation-comments.md) adds
`qleisli doc <source-file>`, `parse_documented_module` and Markdown rendering.
The source parser validates Rust-style doc placement using a sidecar distinct from the
public AST. The M1 extension separately adds AST fields/variants. Documentation is returned separately; `doc` only parses one
file and does not resolve imports or check types, ownership or contracts.

The CLI preserves the source-root argument as an OS path, including non-UTF-8
paths where the filesystem permits them. Human-readable path displays may use
replacement characters; filesystem access uses the original path. Invalid
commands return usage status 2, and source-loading failures return status 1.

```sh
cargo run --bin qleisli -- check examples/bell
cargo run --bin qleisli -- run examples/bell
cargo run --bin qleisli -- run examples/phase_oracle
cargo run --bin qleisli -- run examples/feedback
```

<a id="検査と変換の規則"></a>

## Checks and lowering

These implementation correspondences are separate from general mathematical
proofs. The [conformance record](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/specification-status.md) distinguishes the
normative rules, capacity profile, finite tests, and open obligations.

| Form and classification | Type, ownership, and effect | IR correspondence |
| --- | --- | --- |
| Function call; language form | Resolve declarations and explicit imports in the defining module. Check argument count/types, result, and declared effect. Reject all call cycles, including unused bodies. | Move arguments and expand the body with fresh IDs. No first-class operation values. |
| `let` and block; language forms | Move any value containing `Q<A>`. Copy classical values. Evaluate the right-hand side first; reject shadowing live ownership or dropping it with a wildcard/statement. Return or explicitly consume block-local ownership. | Binding alone adds no quantum operation; subsequent operations use the current token. |
| `basis fn`; language form | `Unit`, `Bit`, and finite products only; enumerate every input. Logical operators and basis calls use a separate context. A multi-parameter declaration has a left-associated semantic product domain, with the first argument in low bits; ordinary calls still require separate arguments. | Compile to a total finite table. A basis function need not itself be injective. |
| `do x <- q; pure e`; language form | Consume `q:Q<A>`, check totality and injectivity of the expressible map to `B`, return `Q<B>`. Equal width is `Unitary`; growth is `Iso`. | `LiftBasis` preserves existing ordered wires and appends fresh wires if needed. |
| Gates, `split/join`, observations; sealed operations | Use the [sealed contracts](standard-library.md); compare exact source product trees. Toffoli returns `((a,b),t)`; `measure_z` returns only `CBit`. | Emit the corresponding constructor, including distinct `Gate`, `Cnot`, and `Toffoli`, and independently reverify. |
| Classical `if`; language form | A `CBit` condition selects exclusive branches with matching result types and outer consumption. Retain caller and pending resources. | Merge result positions and the complete surviving frame with fresh quantum phi IDs and classical phis. Branch-created wires may be returned. |
| `with_computed`; language form | Consume/return `Q<A>` with a total predicate into `Bit`. Its body sees classical captures and one private auxiliary, not outer quantum values. The auxiliary may hide a masked outer name without consuming that outer resource. | Certify an expanded auxiliary identity or Z/T chain, then emit atomic `ComputeUseUncompute`; no standalone `Release0`. |
| Three-argument `with_computed(q,f,u)`; finite semantic language extension | Consume/return `Q<A>`; isolated binders own the data and one computed bit and return both. No outer captures. Require an explicit eligible static unitary u on the exact source type. | Retain the predicate, joint body W and logical u in `CertifiedCompute`; independently check `W E_f=E_f u`. See [specification and bounds](semantic-contracts-v0.1.md). |
| `apply_contract(implementation,specification,input)`; finite semantic language extension | Evaluate input first; require ordinary declared unitary targets with the same exact unary `Q<A> -> Q<A>` signature. Preserve linear ownership, including Unit. | Independently check both concrete raw functions and their exact meaning; retain immutable function evidence in an ordered `CircuitAction::Contract`. See [function contracts](function-contracts-v0.1.md). |

Classical phi inputs are checked before outputs are introduced. A phi cannot
read another output of the same merge. Quantum result-position matching may
pair different original registers: `if c {(a,b)} else {(b,a)}` expresses a
conditional permutation, not cloning or a product-state assertion.

The computed-body certificate is checked after expansion. General preservation
effects in signatures, arbitrary borrowed work registers, and computed bodies
containing classical branches or static transformations are outside the
two-argument form. The three-argument form admits the checked finite unitary
circuit profile, including closed branches and static transformations.
The raw IR's broader protected regions do not provide general source borrowing.
Unsupported cases produce diagnostics instead of a changed meaning.

[Static inverse, repetition, and control](static-operations.md) require a unitary
`Q<A> -> Q<A>` with no classical ports. Closed internal classical computations and selected branches are resolved
during flattening, after both arms are checked. A body is independently verified before
flattening into a finite sequence with exact eighth-root phase indices and
output-axis permutations. Repetition counts are limited to 0–4,096, and copying
tables and steps spends the common expansion budget.

<a id="受理拒否の例"></a>

## Accepted and rejected examples

Assume appropriate imports and declaration types.

| Example | Decision |
| --- | --- |
| `do x <- q; pure (x,x)` | Accept when it fits the profile: distinct basis inputs have distinct images. This can use a whole product basis value. |
| `with_computed(q,p) { \|a\| phase(a) }`, where `phase(a) { z(a) }` | Accept after checking the expanded phase chain. |
| `if b { x(r) } else { r }` | Accept: both branches return the same input ownership. |
| `(q,q)`, or `h(q)` after `measure_z(q)` | Reject reuse of consumed ownership. |
| `let _ = init0();` or `init0();` | Reject implicit quantum disposal. |
| `do x <- q; pure 0` for `q:Q<Bit>` | Reject the well-typed but noninjective lift. |
| `do x <- q; pure xor2(x)` for `q:Q<(Bit,Bit)>` and the bundled `xor2` | Reject argument count: a product is not unpacked into two parameters. |
| `measure_z` in `iso`, or `init0` in `unitary` | Reject the effect violation. |
| Auxiliary `h(a)`, measurement, or an attempted capture of outer quantum ownership | Reject the certificate, effect, or ownership violation. |

`do (a,b) <- q; pure (a,a xor b)` destructures basis products before
constructing the complete lift table. `do (a,_) <- q; pure a` removes a `Unit`
factor but rejects a discarded `Bit` factor by the full-domain injectivity
check. Ordinary `true`/`false` and `not`/`and`/`xor` use `CBit`; both operands
are evaluated exactly once in order, including observation effects. The two
new literal keywords are reserved. See the [language specification](language-spec.md)
and [specification boundary suite](../tests/specification_boundaries.rs).

<a id="診断と上限"></a>

## Diagnostics and limits

`CompileError` contains an `ErrorCode`, file path, UTF-8 byte span, one-based
line/Unicode-character column, and explanatory message. Line tracking supports
LF and CRLF; bare CR is a located lexical error since 0.2.0. Consumers can inspect the category instead of matching free
text. Lower-level `ParseError`, `ProjectError`, and `ValidationError` do not all
have equivalent enum categories.

The current categories distinguish `Arity`, `TypeMismatch`, `Effect`,
`UnknownName`, `RecursiveCall`, `Ownership`, `InvalidEntry`, `Unsupported`,
`Limit`, `Project`, and `InvalidIr`. In this implementation, `Ownership` also
covers a noninjective coherent lift; it is not limited to duplicate handles.
A basis call with too few arguments fails as `Arity` before its resulting map
can be tested for injectivity. Parse and project-loading failures are wrapped
as `Project`. These are diagnostic conventions, not additional source effects.

Ordinary argument type errors point to the caller's actual expression; arity
errors point to the call. This holds across modules. Errors in a callee body
point to that body. Ordering among multiple violations and exact message text
are not normative.

Independent IR-validation errors use a private operation-path/source-span map
to identify the originating expression, including nested classical branches
and isolated computed bodies. Errors without a mapped operation fall back to
the enclosing declaration or static-operation site. This diagnostic metadata
does not participate in IR acceptance. Exact contract mismatches include the
first differing zero-based input column and output row with exact actual and
expected entries. These are the logical input and physical output basis labels
in the checked equation's declared order, not measured outcomes. Parser errors
include `parse error:` in their message while retaining the public `Project`
category; contract failures retain `InvalidIr`.

In 0.1.9, function-effect failures locate a cause of the strongest derived
effect and name both derived and declared effects. Declared callee effects
remain binding even for an empty body; callers point to their own call site,
and both classical arms are checked. This provenance is diagnostic metadata,
not a new acceptance rule. Grouped imports are supported in 0.2.2 by expansion to existing import leaves.
Static `h/x/z/t` arguments still show a closed unary wrapper. The
[repair tests](../tests/repair_diagnostics.rs) check those rewrites.
The frontend still reports one error per invocation; collection/recovery is
[A020-11](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/v0.2.0-backlog.md#a020-11--independent-errors-require-repeated-checking-rounds).

Module-import cycle detection uses an explicit DFS stack. Import-chain depth
does not consume the Rust call stack; cycles still report the importing file,
the closing `use` span, and the cycle path. This graph traversal is separate
from the syntax and function-expansion limits below.

A register or basis function's input/output width is at most 12 bits. Syntax,
expression/call expansion, and basis evaluation have depth limits of 64.
Internal type/value trees have at most 4,096 nodes and depth 64, including the
basis-type tree attached to a quantum value and zero-bit Unit products.
Annotations, inferred basis types, and computed-predicate product domains are
checked; excess yields `Limit`.

Statements, evaluation, expansion, finite tables, constructed/copied trees,
environment/register snapshots, and phi construction spend a shared work budget
of 1,000,000. Since 0.1.9, source retention spends one unit per source byte
**once per compilation**, when the first static-provider or `apply_contract`
receipt needs it. Both paths share one immutable snapshot containing all loaded
modules, comments and bundled std sources, including unimported modules.
Before copying, the frontend checks the remaining work and the existing
evidence metadata bounds (128 modules, 4,096 bytes per module name, 1 MiB for
source records including names). Each receipt independently checks the complete
metadata, including its implementation/specification names, against the same
evidence profile and exact-check budget. Distinct contract pairs still charge
their copied raw representations and pair names under
[FC-CACHE](function-contracts-v0.1.md). No source byte is multiplied by receipt
count in the shared lowering budget. This resolves
[A020-10](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/v0.2.0-backlog.md#a020-10--source-snapshot-copies-exhaust-the-shared-lowering-budget)
without changing the public owned identity API or increasing a limit. Explicit
public identity inspection may materialize one bounded owned compatibility view
per receipt; compilation, checking and execution do not require that copy.
Every declaration is checked independently, and each ordinary call is inlined
at each use; the 1,000,000-unit budget is shared by the whole loaded project.
A shallow doubling call graph can therefore exhaust it. The limit diagnostic
now locates the declaration being checked and names the inner location where
the next charge failed, with used/requested work. It does not attribute all
project cost to that inner expression. The [review reproduction](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/reviews/v0.2.0.md)
retains this finite limit; hierarchical sharing remains pending under A020-03.

These checks bound exponential nonrecursive expansion and classical
copying as well as quantum data. They are implementation limits, not limits on
the mathematical finite types. The simulator has separate
[capacity and numerical limits](ir-prototype.md#参照実行系の範囲).

Since 0.2.0, exact arithmetic and verification additionally share **10,000,000
units per compilation**, including static arguments unused by their callees,
function receipts and closed static transformations. Matrix operations charge
their conservative full cost before execution. Shared immutable source storage
is charged once per allocation within this budget; metadata validity is still
checked on every receipt. This newly aggregate restriction is a MINOR change,
not a retroactive interpretation of 0.1.9's lowering-only bound. It bounds
specified work, not elapsed wall time or whole-process memory. There is no flag
to reset it per call; reduce the derivation or wait for the separately gated
hierarchical profile. Source-byte overrides do not override exact work.

On macOS, descriptor-relative `openat` with `O_NOFOLLOW` acquires each path
component atomically while retaining its parent descriptor. It does not require
`O_NOFOLLOW_ANY` or raise Rust's existing minimum deployment target.
On Linux x86/x86_64, ARM/AArch64 and RISC-V, held directory descriptors and
no-follow opens provide the corresponding protection; readable `/proc/self/fd`
is required and failure does not fall back to following links. Opened sources
must be regular files; nonblocking acquisition avoids hanging on a substituted
FIFO. Other targets retain the old filesystem trust assumption. This is not a
filesystem sandbox, nor does it freeze files against concurrent in-place writes.
See the [review disposition and platform validation](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/reviews/v0.1.9-followup.md).

<a id="確認した結果と残件"></a>

## Evidence and remaining obligations

| Source project | Ideal result | Finite evidence |
| --- | --- | --- |
| `examples/bell` | `00`, `11`, each with probability 1/2 | Source checking, IR verification, and reference execution. |
| `examples/phase_oracle` | `1` with probability 1 | Expanded auxiliary phase followed by interference. |
| `examples/feedback` | `00`, `10`, each with probability 1/2 | Measure one Bell half and conditionally correct the other. |
| `examples/grover` | `11` with probability 1 | Shared preparation, oracle, and one reflection step. |
| `examples/bernstein_vazirani` | `10` with probability 1 | Reuse Hadamard preparation and recover the hidden linear function. |
| `examples/bit_flip_code` | `11000` with probability 1 | Middle X error: syndrome `11`, logical X result `0`, decoded auxiliaries `00`. |
| `examples/phase_estimation` | `1001` with probability 1 | T phase 1/8 as low-bit-first `100`, followed by target Z result `1`. |
| `examples/order_finding` | `000,010,001,011`, each with probability 1/4 | N=15, base 2; the Rust Shor example obtains factors 3 and 5 or a retry, each with probability 1/2. |

The [compiler suite](../tests/compile.rs) covers caller frames, branch-created
wires, mixed phis, exact types, primitive operations, rejection, source locations,
and work limits. In particular, growing values and Unit trees are diagnosed on
a 2 MiB thread stack, with accepted in-budget counterparts. Other suites cover
[source judgments](../tests/source_judgments.rs),
[source semantics](../tests/source_semantics.rs),
[static operators](../tests/static_semantics.rs), and
[instrument regressions](../tests/source_soundness.rs).

The [project suite](../tests/project.rs) exercises deep import chains and cycles
on a 2 MiB thread stack, as well as shared dependencies. The
[CLI suite](../tests/cli.rs) covers ordinary paths and, on Unix, non-UTF-8
arguments. Existing non-UTF-8 source directories are also tested on Linux.

Historical milestones were 92 Rust tests at A2 and 108 when v0 was fixed. These
are not current totals; subsequent runs are recorded in the
[conformance record](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/specification-status.md). The A2 static-operation suite
covers phase distributions, reflection signs, references, inverses, rejection,
malformed raw IR, and expansion limits. Algorithm suites independently check
Grover/BV inputs, bit-flip assumptions and correlations, parity coherence, and
[arithmetic/order-finding cases](arithmetic-order-finding.md#検証結果).
No new trusted primitive is introduced by the ordinary library definitions.

The Stage 3–4 minimum path is connected. The source rule system's paper proofs
and local Lean results do not prove general correspondence with every Rust
acceptance or lowering path. That adequacy and source-to-IR meaning preservation
remain Stage 1 priorities. General borrowing, operation parameters, literal
auxiliary execution as an independent comparison, exact reference execution,
and backend capability checks remain later work. Distinct ownership never
implies state separation.

## Machine-readable check and run results

The 0.1.7 development tree adds `--format=json` to `qleisli check` and
`qleisli run`, using [qleisli.result version 1](machine-interface-spec.md#diagnostics).
The flag opts into one JSON result, including failures; human output remains
the default. This is M1 X1 under the user's explicit version exception, not
a new `.qli` form or checker rule. Structured diagnostic APIs retain parser
provenance and source coordinates while existing error records remain compatible.
Other M1 commands and formats are not implemented.
