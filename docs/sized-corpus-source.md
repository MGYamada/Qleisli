# Sized source: Rust pipeline and Python oracle

The 2026-09-29 user instruction puts corpus implementation before further
general proof infrastructure. This bounded experiment connects actual source
to the existing hierarchical IR and fresh independent inspection. It does not
change the production `qleisli check/run` grammar or assert source adequacy.
The [Rust source pipeline](#additive-rust-source-pipeline) checks generic size
obligations under `requires` and branch/fold guards. The Python script is an
untrusted concrete-instantiation experiment and differential oracle. Its
historical concrete source contract appears first below. The two checking
scopes are explicit; a successful concrete example does not discharge a generic
obligation. CI compares their shared subset and retains intentional differences.

## Historical Python concrete source contract

Each module file contains explicit imports and one public unitary function. Static
parameters have type `Nat`, or the bounded `Op<Bits<e>>` entry parameters
described below; instantiation supplies every parameter explicitly.
Types are `Q<Bit>`, `Q<Bits<e>>`, or arity-preserving tuples of these types.
The instantiated natural expressions allow literals, variables, `+` and `-`;
subtraction must have a nonnegative result. This is a concrete subset of the
[adopted linear fragment](size-expressions.md), not a universal size solver.

Bodies contain linear `let` bindings, tuples, imported primitive applications
and `for static k in lo..hi carry state = initial { ... yield next; }`.
The range is half-open; `hi < lo` rejects. A fold transfers its complete carry
value, preserves its exact type at every executed step, and returns the initial value
when empty. Each quantum variable is moved exactly once, even at width zero.
Each iteration owns a separate scope. Capturing live quantum owners outside
the carry is rejected. Move/arity checking also visits an empty fold body;
size and index checks apply at concrete executed instantiations. Bindings may shadow consumed names but cannot silently
discard live values. Return types and tuple shape must match exactly.

Primitive imports resolve `std::quantum::{h,x,cnot}` and
`std::registers::{take_bit,put_bit}` (one import per name). The QFT extension
below adds a controlled-phase adapter. Ordinary imports use `module::function`
from explicitly supplied source modules; the command-line tool loads sibling
`.qli` files, with at most 64 modules. Every import resolves its declaration,
including unused imports. Arbitrary names and aliases never become primitives.
The function name has no algorithm meaning.

* `h` and `x`: consume and return one `Q<Bit>`, with the usual phase-fixed
  matrices, lowered to an independently reconstructed one-bit finite leaf.
* `cnot`: consumes two distinct `Q<Bit>` values and returns them in order,
  mapping `|a,b>` to `|a,b xor a>` with scalar +1. Lowering uses coherent
  control of the same finite X leaf.
* `take_bit[n,k]`: consumes `Q<Bits<n>>`, requires `k<n`, and returns
  `(Q<Bit>, Q<Bits<n-1>>)`. The first output is axis k; other axes retain order.
* `put_bit[n,k]`: the inverse typed conversion, inserting the first argument
  at k in the second argument. Both structural operations allocate fresh
  owners and retain the empty owner when n=1.

Frames and routing are explicit tensor, sequence and rewire nodes. The untrusted
producer normalizes routing through ordered axes, tensors independent gates,
and factors consecutive CNOTs sharing a control. Parallel register layers keep
recursive tails; one-bit boundaries use explicit `bits_to_bit` and inverse
conversions. Recognition examines actual gates and axes, never the function
name. Production integration still requires source preservation for these
transformations; current complete basis/reference tests are regressions.
Only the index-dependent static fold is concretized; no quantum truth table or dense
whole-register matrix is generated. Existing eight-bit register, 16-wire,
six-bit finite-leaf and verifier work limits still apply. Development limits are 64 KiB of source,
10,000 tokens, delimiter depth 64, AST depth 128, 1,024 fold iterations and
1,024 source operation calls in total across module instantiation, and 10,000
generated definitions. This experimental entry point adds no restriction to
an existing production API.

## QFT-driven extension

The shared QFT source uses `requires e >= e`, `e <= e` or `e == e` for
static entry premises, and `if static predicate { body } else { body }` for
guarded routing. Instantiation checks the premise before lowering. Both branches
must transfer the entire live quantum context and have the same tuple shape;
concrete type/index checks occur in the selected branch. This experiment does
not yet prove generic type/size obligations under symbolic assumptions.
Comparisons are outside size expressions; division and nonlinear products stay
unsupported. Source predicates are never passed to the verifier as evidence.

`std::quantum::controlled_phase[j,k]` is an experimental untrusted adapter,
not a new primitive acceptance rule or production standard API. On two distinct
`Q<Bit>` arguments it applies `exp(2*pi*i*j*a*b/2^k)`, returning both owners in
order. Require `0 <= k <= 8` and `0 <= j < 2^k`. It emits the existing closed
dyadic-phase node and coherent control node. Guarded explicit take/put operations
implement output reversal; it is neither size equality nor canonical reshape.

When the complete elaborated gate trace matches a positive dyadic Fourier
staircase and the result axes explicitly reverse the input, the untrusted
producer may factor that trace into the existing shared-gradient construction.
Matching includes every gate, axis and exact rational phase. A changed body
must not silently become a correct Fourier circuit. The independent named
Fourier request still checks the actual generated artifact and all finite H
obligations. Other gate traces use ordinary lowering, subject to the same
limits. This optimization is separate from a general source-preservation proof.

Ordinary calls `f[n] (q)` and `adjoint(f[e,...],q)` reuse imported
same-type unitary definitions. The arithmetic extension below also permits
multiple explicit quantum arguments. Resolve all explicit natural arguments
and preserve the complete input/output type. A module/instantiation
is compiled once per importing producer; repeated calls reference that shared
definition through explicit boundary adapters. Cyclic instantiation rejects,
and source-call depth is bounded by 32. Generation work is aggregate, not reset
at each module. Adjoint wraps the actual shared unitary graph in the existing
inverse rule; it never recognizes a function name as a known inverse.
Quantum arguments move, and all local results/owners remain checked.
The QPE extension below supports controlled use of explicit transparent entry
providers. The client extension below now forwards them through ordinary module
calls; the remaining static-operation constructors are still pending on this
path. The existing production static-operation contract is unchanged.

The `--adjoint` option is also retained as a development wrapper for an actual
unitary artifact. Both paths reuse its forward definition/evidence without a
second algorithm body or dense matrix. The QFT inverse source is the actual
ordinary-call/adjoint client used in corpus validation.

## QPE-driven extension

An experimental unitary entry may declare `static U: Op<Bits<e>>` alongside
natural parameters. Comma-separated `requires` clauses conjoin size predicates
and explicit `Apply(U)`, `Adjoint(U)` or `Controlled(U)` access requirements.
These names must refer to declared operation parameters and may not repeat.
Runtime bindings and fold indices cannot shadow static parameters.

For an operation parameter, `controlled(S)(control,target)` consumes two distinct owners
of type `Q<Bit>` and `Q<Bits<e>>`, and returns them in the same tuple order with
unitary effect. Its phase-fixed meaning is identity in control sector zero and
S in sector one. `S` is an operation parameter or `repeat_op(count,S)`;
controlled use requires **declared Controlled access** even when the count is
zero or the enclosing static loop is empty. Apply and Adjoint do not grant it.
The current experiment implements only this controlled parameter use, not
direct application or parameter adjoint. Access is checked in every static body.

Counts are concrete naturals through 256 or `2^k` / `2^(e)` with exponent at
most eight; the product of nested counts is at most 256. A compound exponent
requires parentheses: `2^k+1` rejects instead of changing precedence silently.
This bounded count syntax is separate from affine type sizes. `Bits<2^n>`
continues to reject. Every child is checked even at count zero. Ordinary
repetition and control nodes reference the shared body; they do not materialize
large matrices or hide execution multiplicity.

The development Python API supplies `Operation("module::function", (sizes, ...))`;
the CLI uses `--operation U=module::function:N,...`. Providers must be actual
source modules with a single identical quantum input/output type and natural
parameters. Their complete bodies are source-checked, including unused or
zero-repeat providers; there is no opaque provider or Boolean evidence flag.
Used provider graphs, including zero-repeat children, remain in the proposal
for fresh native/finite checking. A compiled source body alone is not trusted
acceptance evidence. `--module NAME=FILE` supplies an explicit extra module,
for example the same shared Fourier source from its corpus directory.

The `std::quantum::phase[j,k]` adapter consumes/returns `Q<Bit>` and applies
`diag(1, exp(2*pi*i*j/2^k))`, using the same normalized dyadic bounds as
controlled phase. It lowers to the existing phase rule. It is an untrusted
adapter, not a new sealed primitive or production standard API. Ordinary
`hadamard_bits`, `evolve` and `estimate` definitions form the actual QPE corpus.

Independent one-axis gate layers can retain recursive register tails rather
than unpacking every bit. The Fourier trace optimization now lowers its
explicit output reversal recursively through take/put, identity tensor and
rewire. Both changes preserve explicit typed permutations; neither makes
reversal a type equality. They are untrusted optimizations tested against full
phase/reference formulas and the existing named forward Fourier checker.

The [coherent QPE source](../corpus/sized/qualtran_qpe/README.md) accepts arbitrary
phase-register input and retains both quantum registers. Sizes (1,3) and (2,4)
pass native inspection and full-column/reference diagnostics. The historical
(8,8) proposal exceeded the unchanged structural budget, including when the
controlled powers were tested without preparation or QFT. The 2026-09-30 user
decision limits remaining validation to small qubit systems and removes further
maximum-size checks from completion requirements; the old failure stays recorded.
Initializing the
phase register and measuring it into `CBits<m>` are now exercised by the
initializing/observing continuation below. Independent named QPE binding and
production execution remain open; diagnostic branch vectors do not close them.

## Arithmetic-driven extension

The [shared AddK/Equals sources](../corpus/sized/qualtran_arithmetic/README.md)
add ordinary multi-argument calls and controlled use of transparent imported
definitions. For a function with parameters `q0:T0,...,qk:Tk`, an ordinary call
supplies exactly those arguments, preserving each type and tuple shape. Its
output must be the complete input group: T0 for one parameter, otherwise
`(T0,...,Tk)`. A tuple-valued single argument remains distinct from several
arguments. This adds no implicit conversion between owners or basis types.

`controlled(f[n,...])(c,(q0,...,qk))` consumes a `Q<Bit>` control and the
explicit complete input group of an imported ordinary definition. It returns
`(c,(q0,...,qk))` in the same nested shape, with unitary effect, acting as
identity when the control is zero and as the actual phase-fixed body otherwise.
For one parameter, supply that parameter directly as the second argument.
`adjoint(f[n,...],(q0,...,qk))` similarly accepts the complete group and wraps
the actual body in the existing inverse node. A transparent body supplies the
construction; an abstract operation parameter still requires its declared
access. These language forms emit existing control/inverse/sequence/rewire
rules; none is a new sealed operation or a name-based arithmetic rule.
Imported definitions may also occur inside bounded `repeat_op` under control.

All arguments move exactly once. Duplicate aliases, missing owners, wrong
argument count/grouping, different result nesting, and `Bit`/`Bits<1>` mismatches
reject. Move, signature and name-resolution checks visit both static branches
and empty folds. A lexical quantum or static binding hides an imported
operation even after that value has moved; consuming it does not reopen the
function name. Concrete selected branches also check exact types and indices.

Self-import permits bounded concrete recursive instantiation: the arithmetic
sources guard n=0 and recurse at n-1. Re-entering the same module/function and
natural arguments rejects; growing recursion reaches the unchanged depth-32
limit. Aggregate call/fold limits are unchanged. This is finite elaboration
to an acyclic graph, not a generic termination or universal type-size proof.

Imported artifacts share identical graph/evidence entries after remapping
preceding references. Equality includes the complete quantum interfaces,
actual bodies, meanings, rules, premises, identity encodings and finite bytes.
It does not trust names, submitted receipts or a hash-only equality claim.
Every retained equation still passes independent inspection, including children
of zero repeats. Factoring Equals' repeated complement into an ordinary source
helper, together with this structural sharing, admits width three under the
unchanged budget. Sharing storage/verification does not erase repeated work
during execution.

The source and [validation record](../corpus/sized/arithmetic-validation.json)
cover widths 0–3, local empty owners, wraparound constants, phase/reference
behavior and incorrect carry/restoration counterexamples. Independent named
arithmetic binding and production source integration remain open. AddK's
reference implementation repeats increment K times; it does not establish
efficient general arithmetic synthesis.

## QPE client operation forwarding

The [local order/amplitude clients](../tests/fixtures/sized_clients/README.md)
both call the same retained QPE definition. Ordinary bracket arguments now
follow the callee's complete declaration order, distinguishing natural arguments
from static operation parameters. An operation argument is an existing static
parameter or an explicitly instantiated transparent ordinary definition, such
as `estimate[n,m,U]` or `estimate[n,m,grover[n,j,d]]`. It is not a runtime value,
closure, guessed provider or new primitive. The runtime owner group and unitary
effect of an ordinary call are unchanged.

When forwarding a parameter, the caller must declare every access required
by the callee. This check visits empty folds and unselected branches as well
as executed calls. Apply/Adjoint never imply Controlled. A transparent argument
is checked recursively against the callee's exact instantiated `Op<Bits<e>>`
type, with its actual source body, premises and all nested provider assignments.
The known-body construction can then use the existing inverse/control rules;
as in the [M1 transparent-provider contract](next-minor-spec.md), this does not
grant transformations to an opaque oracle merely from mathematical unitarity.
Direct parameter application/adjoint and additional static constructors remain
outside this experimental source slice.

The instantiation key includes function, all natural arguments and the complete
nested provider assignments. Equal sizes with different operations must not
reuse stale generated circuits. Actual identical graph/evidence entries may
still share after complete-content comparison. Provider nesting is bounded by
32, and existing aggregate generation/inspection budgets remain in force.
The Python `Operation` descriptor accepts nested named provider assignments;
the CLI's `--operation` option still supplies a flat transparent definition.
Nested composition can be written in source instead.

Small-system validation retains full complex phases, arbitrary phase-register
inputs, residual target/reference columns, p=0/1 and off-grid amplitude trials,
plus a phase-sensitive nested-provider cache case. No measurement, certified
classical probability evaluation, named order/amplitude contract proof or
production frontend transfer is claimed by those numerical diagnostics.

## Initializing and observing source continuation

The resumed measured-source experiment adds a separate untrusted
`compile_sized_instrument.py` producer. It parses `iso` and `observe` ordinary
functions, empty runtime argument lists, classical `CBit`/`CBits<e>` types and
the classical unit value/pattern `()`. Quantum values and mixed tuples still
move; classical values/tuples may be copied or left unused. Both static branches
and empty folds receive name, shape, move and effect checks. Selected concrete
instantiations also check exact widths. Effect ordering is Unit­ary < Iso <
Observe; a false branch cannot hide a stronger effect. Pure source and operation
providers continue through the existing unitary producer and shared definitions.

The retained [second source attempt](../tests/fixtures/authoring_sessions/measured-qpe-v021/attempt-02/measurement.qli)
calls ordinary recursive initialization/readout helpers around the same QPE body.
The experimental adapters below are producer intrinsics, not additions to the
bundled stdlib or production grammar:

- `std::quantum::init0()` is the existing sealed one-bit zero preparation,
  with Iso effect and a fresh owner/axis. `std::observe::measure_z(bit)` is the
  existing consuming Z measurement with Observe effect, returning `CBit`.
- `std::registers::empty()` and `consume_empty(q)` explicitly create/consume
  `Q<Bits<0>>` through the existing structural rules; they neither allocate a
  physical qubit nor authorize release of a nonempty register.
- `std::classical::empty_bits()` constructs `CBits<0>`;
  `prepend_bit[n] (bit,tail)` constructs `CBits<n+1>` from `CBit` and `CBits<n>`.
  These are ordinary classical data-construction adapters with no quantum effect.
  The first bit occupies position zero. They emit an explicit pack proposal,
  whose order is checked separately; naming the helper is not semantic evidence.

The resulting proposal has an initialization prefix, a coherent segment and a
readout suffix. Source operations may interleave: the untrusted producer hoists
fresh independent zero preparations and postpones measurements across operations
on other logical owners. This uses disjoint local actions, not a product-state
assumption: arbitrary entanglement with the retained target/reference must
survive. Classical outcomes can only be copied/assembled in this source slice;
runtime classical branches or outcome-dependent quantum actions remain
unsupported and must not be silently retimed. Structural conversions remain explicit
checked nodes. No measured owner can be reused in
source. The result proposal keeps initialization nodes, the shared pure graph,
measurement nodes and classical packing separate, with complete matching frames.
Each boundary still needs independent checking and composition; this producer
does not itself issue a receipt or prove source/retiming preservation. Source
allocation uses distinct axes, with a sixteen-axis aggregate cap even when an
earlier owner has been measured; it does not silently reuse a physical wire. The selected
small-system validation and existing aggregate source limits remain in force.

Each ordinary helper retains its local quantum frame so recursive initialization
and readout do not repeat the caller's complete frame at every operation.
The untrusted compactor composes adjacent rewires, removes exact identities,
flattens single-use sequence wrappers and retains shared inverse/control/repeat
bodies, including zero-count children. A wire-only Bit/Bits(1) conversion with
a balanced internal empty-register lifecycle can use the existing explicit
conversion rule; an empty input/output owner cannot be erased by that rewrite.
Complete endpoint types/ports and before/after phases are regression-checked.
This is producer optimization, not a new checker rule or preservation theorem.

The [measured-source results](../tests/fixtures/authoring_sessions/measured-qpe-v021/instrument-validation.json)
cover ordinary initialized QPE, order/amplitude CBits clients and an interleaved
measurement/local-gate/fresh-preparation example with reference columns. The
small `(2,4)` wrapper still exceeds the unchanged structural budget. That report invokes preparation, pure graph and readout separately. The later
[host connection](../tests/fixtures/authoring_sessions/measured-qpe-v021/host-instrument-validation.json)
checks four small source clients together through `Kernel::check_instrument`,
including all finite obligations. Its baseline-derived requests are mutation
regressions, not independent named QPE evidence or production source integration.

## Acceptance and limits

The native Lean checker inspects the generated artifact and Rust reconstructs
all actual finite equations. The diagnostic executor then evaluates that same
artifact against independent algorithm formulas, including complex reference
columns. Numerical comparisons are tests, not acceptance evidence for an
independently named algorithm contract. These Python experiment results do not
establish production integration, source preservation or named `CBits` client
contracts. The Rust continuation below records its own coverage; universal
source preservation, remaining operation constructors and R14/H1–H5 gates
remain separate obligations.

This experiment changes the development order, not the trusted boundary or
release criteria. Preserve fixed translations and historical failed sources.

## Additive Rust source pipeline

The resumed continuation adds `frontend::sized` as an **untrusted source
preparation API**, separate from the finite frontend. It retains complete source
text and byte positions in an opaque parsed program; its syntax representation
is private. Sized identifiers and keywords are contextual to this entry point,
so the existing public AST, lexer, loader, compiler and CLI keep their contracts.
Parsing and elaboration produce no hierarchy seal. The bounded lowering and
separately checked `qleisli sized` entry point below build on these source values.

This bounded profile starts with the existing measured-QPE modules: one ordinary
function per module, explicit imports, natural/operation parameters, Bit/Bits and
CBit/CBits types, tuples, linear bindings, static branches/folds and transparent
calls. Generic checking must inspect both branches and empty fold bodies for
names, capabilities, effects and linear ownership. Subtraction and register
indices require implications from natural-number assumptions, declared premises
and branch/fold guards; checking one convenient size is insufficient. Solver
exhaustion or an unsupported obligation rejects without issuing evidence.
`ParsedProgram::parse` checks an explicit module/text map; `load` reads an explicit
module/file map using the existing regular-file loader. `instantiate` records
concrete `u32` entry naturals and transparent providers after checking their
signature types and premises. It does **not** elaborate calls/folds, check every
concrete phase/repetition capacity, or generate executable IR. Parameter Apply
and Adjoint forms can be prepared when their access is declared; this adds no
execution support to the experimental Python producer. Body elaboration is a
separate step; source preservation and independent acceptance remain obligations.

Preparation limits are 64 modules, 64 KiB per module, 1 MiB total, 10,000 tokens
per module, syntax nesting 64, natural-expression depth 128 and tuple arity 64.
Inferred types have depth at most 64 and 4,096 cells; a scope retains at most
16,384 type cells, including copyable classical values. These checks also bound
flat source that repeatedly doubles a nested tuple.
Linear implication uses checked `i128` arithmetic and a rational relaxation:
at most 32 variables, 64 assumption alternatives, 4,096 generated constraints
and 50,000 elimination pairs per query. Only a proved contradiction discharges
an obligation; failure or incompleteness rejects. All sizes remain natural, with
guarded subtraction; nonlinear symbolic products and general predicates reject.
These are preparation budgets, not runtime/resource-safety guarantees.
Preparation does not adopt the complete G020-1 grammar or prove frontend adequacy.

`Instantiation::elaborate` is the next additive preparation step. It produces an
opaque, untrusted source-order program with shared concrete function definitions,
ordered operation steps, original spans, exact type trees and explicit quantum
owner/classical-value identities. Calls and operation repetitions retain references
to shared definitions; only static folds elaborate their concrete iterations.
Initialization, observation and classical packing retain source order. Every
supplied operation provider is elaborated even if its parameter is unused, and
zero repetitions still validate their child. Unselected static branches retain
their generic checks; they do not execute or acquire artificial concrete size
premises. Concrete guards, phase parameters and repetition capacities are checked
on the selected bodies and all supplied providers. This intermediate form has no
interchange schema, IR seal, execution API or preservation theorem.

Elaboration permits eight-bit registers/classical sequences and at most 16 live
quantum wires, including suspended caller owners during a child call. It retains
the existing dyadic bounds (`k <= 8`, `j < 2^k`) and repetition counts/products
through 256. Construction budgets are 1,024 specialization requests (cache hits
included), 1,024 concretized fold iterations across newly built definitions,
call depth 16, 10,000 retained source steps and 100,000 retained value-tree cells.
The combined active function, block, expression and static-provider traversal
depth is also limited to 64, so nested syntax cannot multiply the call allowance.
Each concrete value is limited to 4,096 cells (including its stored type trees),
and each scope to 16,384 value cells before lexical scope copying.
Shared calls and repetitions are not expanded into gate lists; these budgets and
the reported source peak are diagnostics, not certified execution-work bounds.

`ElaboratedProgram::lower` emits an opaque `HierarchyProposal` in the existing
hierarchical/instrument transport, retaining its complete source-order elaboration.
`ElaboratedProgram::check_lowering_profile` preflights the concrete root before
graph construction. Supported roots are quantum-only `unitary` functions and
`observe` functions returning one chronological `CBits` value plus any residual
quantum owners. Classical entry parameters and `iso` roots receive a located
`unsupported` diagnostic naming the lowering profile. Generic source checking
and concrete elaboration keep their broader contracts.
Its payload, pure graph and proposal-derived comparison request are **untrusted**.
Pure calls and operation providers share graph bodies; only H/X primitive leaves
use exact finite matrices. Structural register/owner transitions determine explicit
axes and remain recorded in the source proposal. Gates and initialization after
observation reject. Fresh `init0` may move before preceding unitary steps only
through the explicit stable-extraction certificate below. Structural views of
remaining owners and classical packing may follow observations; their boundary
representation remains distinct from general source preservation. Output is
quantum-only for pure roots, or one chronological `CBits` result with residual
quantum owners for measured roots; classical entry values are unsupported.
Fresh native reconstruction remains mandatory. A generated comparison request
describes the proposal itself; it is not an independent named-QPE specification,
source-preservation proof, production seal or external-schema enablement.
Proposal construction is bounded by 10,000 definitions, 16 MiB retained graph
descriptor/cache text and 16 MiB per serialized payload/request/precursor, with
1,024 observing call visits and depth 16. H/X leaves are shared and independently reconstructed.
Small native regressions cover QFT widths 1–3, arbitrary coherent QPE inputs,
measured QPE `(n,m) = (1,1),(1,2),(1,3),(2,2)`, order readout, zero-width owners and
the phase-sensitive Grover provider and amplitude readout `(1,2)` including its
preparation prefix. These cases pass the unchanged native checking budget.
Fourier factoring compares complete phase-sensitive traces, including root
definitions. It permits exchanges of disjoint actions and diagonal phases,
while preserving the order of noncommuting actions, exact phase, axes and output
routing. Equivalent schedules produce the same bounded candidate shape.
Export compacts reachable definitions and remaps source-event
references; `lowering_precursor` retains the original source-derived table.
Fixed-seed shots from both actual source clients feed validated modular-order
candidates and finite-grid amplitude estimates, with independent branch/residual
checks. The [validation record](../tests/fixtures/authoring_sessions/measured-qpe-v021/rust-sized-validation.json)
records this bounded coverage.

Ordinary transparent unitary providers may take multiple quantum parameters;
their complete argument group must match the exact result tuple shape. Abstract
`Op<Bits<e>>` parameters retain their single-basis contract. Rust corpus tests
cover GHZ with `requires n >= 1` and the controlled arithmetic helpers, alongside
Python comparisons and independent small-system execution.
The transport profile name `qpe-dyadic8-v1` identifies its bounded angle and
hierarchy format; it does not grant privileges to a function named QPE.

Initialization extraction retains a complete source-event trace: original concrete
definition/step/call path and span, selected values, full quantum frames including
zero-width owners, initialization, observation and classical packing. Each move
lists exactly the preceding pure events crossed. An independent Rust structural
validator replays source bindings, parses actual graph headers/effects, checks
freshness and complete untouched frames, and matches the root's exact ordered
operations and readout; it rejects omitted events, aliasing, changed packing and
extra operations. Candidate generation runs this scan. The public
`validate_initialization_moves` additionally requires a fresh `CheckedInstrument`
with byte-identical payload before reporting this pass as validated. Trace storage
is limited to 10,000 events and 100,000 frame/operand accounting cells.

The checker-free `Qleisli.Semantics.FreshInitialization.commute` equation preserves
full complex amplitudes and arbitrary reference correlations when appending fresh
zero coordinates across an operator on the old coordinates. This equation is
proved; the Rust structural pass is tested, not itself a Lean-proved executable
transform. Source-to-unitary translation and broader source preservation remain
separate obligations. The amplitude client's meaning is `K_m(G) A`, including the
actual preparation prefix; it is not a bare-QPE claim about the original input.


### CLI entry point

`qleisli sized check|run|sample|emit-proposal` requires `--entry=module::function`
and repeated `--module=name=PATH` declarations for the complete dependency closure.
Static bindings use repeated `--nat=name=N`, `--operation=name=module::function`
and `--operation-nat=name.parameter=N`. `check`, `run` and `sample` require an
explicit `--kernel=PATH`; instruments also pass initialization validation.
The optional `--request=PATH` supplies an independent contract. Alternatively,
`--qpe-provider=PATH` supplies the independent provider request for named QPE
checking. The default compares the proposal's own meaning and makes no named-QPE
claim. These two request options are mutually exclusive.
Every successful result includes `verification.scope`, `request_origin` and
`source_meaning_verified`, plus `execution_authority`. The existing `checked`
status is interpreted with these fields. Native failure diagnostics identify
the selected checking mode, source profile and request scope. Capacity failures
state the aggregate structural allowance; the current native failure reply
does not include required work or the exhausted subcomponent.

`run` returns all complex state/branch coefficients from `--basis=N` (default 0).
`sample` is observing-only and requires `--shots=1..1024` and `--seed=N`.
`emit-proposal` requires `--output=PATH` and no kernel; its JSON is untrusted.
The existing finite commands retain their contracts. This bounded Rust route does
not complete general source preservation or the remaining R14/H1–H5 gates.

```sh
qleisli sized run --entry=fourier::fourier \
  --module=fourier=corpus/sized/qualtran_qft/fourier.qli --nat=n=2 \
  --kernel=lean-kernel/.lake/build/bin/qleisli-kernel --basis=1
```
