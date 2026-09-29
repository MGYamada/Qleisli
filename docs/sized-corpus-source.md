# Executable sized-corpus source experiment

The 2026-09-29 user instruction puts corpus implementation before further
general proof infrastructure. This bounded experiment connects actual source
to the existing hierarchical IR and fresh independent inspection. It does not
change the production `qleisli check/run` grammar or assert source adequacy.
Its compiler is an untrusted development tool, like the existing QFT producer.

## Source contract

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
phase register, measuring it into `CBits<m>`, independent named QPE binding
and production execution remain open; diagnostic branch vectors do not close
these gates.

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

## Acceptance and limits

The native Lean checker inspects the generated artifact and Rust reconstructs
all actual finite equations. The diagnostic executor then evaluates that same
artifact against independent algorithm formulas, including complex reference
columns. Numerical comparisons are tests, not acceptance evidence for an
independently named algorithm contract. Production integration, universal
source preservation, remaining operation constructors, measured `CBits` clients, and the
remaining R14/H1–H5 gates are separate outstanding obligations.

This experiment changes the development order, not the trusted boundary or
release criteria. Preserve fixed translations and historical failed sources.
