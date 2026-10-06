# Static values, constraints and bounded specialization

This chapter specifies the implemented static fragment in 0.3.0-alpha, under
the [type boundary](type-model.md) and [authority hierarchy](authority.md).
It records the existing rules tracked by
[#28](https://github.com/MGYamada/Qleisli/issues/28),
[#44](https://github.com/MGYamada/Qleisli/issues/44) and
[#63](https://github.com/MGYamada/Qleisli/issues/63). It does not introduce a
general compile-time programming language. Static helpers and the final loop
surface remain separate work; describing this fragment does not complete those
Issues or discharge quantitative Resource Safety.

## Static categories and binding

The static computation class consists of deterministic, terminating elaboration
computations whose results are admitted sizes, exact constants, closed operation
descriptions or constraint/capability inputs. Its evaluator has only the
explicit static environment and admitted ordinary finite labels; it has no live
quantum owner, runtime input, host environment or execution authority. Results
are normalized/resolved before canonical Core. An operation description must
still satisfy its independent evidence and native acceptance obligations.

This semantic class is the 0.3.0 decision in
[#40](https://github.com/MGYamada/Qleisli/issues/40). It does not stabilize a
general public `static fn`, `const fn` or builder API: those spellings, static
lambdas and quotation/splicing remain choices for #60/#61 in 0.4.0. Any later
0.3.0 helper spelling is provisional unless separately stabilized. Existing
specified forms retain their own contracts; this class alone grants no syntax
or new result type. The bounded constant/helper sugar required by #63 remains
0.3.0 work and is not deferred by the builder-syntax boundary.

`Nat` denotes a nonnegative static integer. It is not a runtime integer or an
ordinary `Bit`. `Basis` denotes an exact finite type tree, and `Op<A>` denotes
a static operation description over that tree. None is a live `Q<A>` owner.
Runtime values, measurement results and quantum owners cannot determine a
static size, operation provider, static condition or loop bound.

Static parameters are explicit, positional and ordered. A parameter's kind may
refer only to earlier parameters. For example, declare `n: Nat` before
`U: Op<Bits<n>>`. Duplicate names and forward kind dependencies reject. Source
calls provide the complete ordered argument list; host entry selection provides
the complete named binding set. Missing bindings are not inferred from a
matching width or provider name.

An abstract Basis parameter remains opaque. Finiteness alone does not permit
type reflection, preparation, tuple decomposition, control or an inverse.
See [generic responsibilities](type-model.md#inference-and-generic-responsibilities)
for the independent access and specialization rules.

## Natural expressions and constraints

The current natural expression grammar contains nonnegative decimal literals,
static Nat names, parentheses, `+`, `-` and `*`. Multiplication binds more
tightly than addition/subtraction; operators at either level associate to the
left. These forms are not runtime arithmetic. Division, remainder, arbitrary
exponentiation and user-defined natural-expression calls are not admitted by
this fragment.

Symbolic normalization produces exact affine expressions over original static
binder identities. Constant folding and multiplication by an expression that
normalizes to a constant are supported. Multiplication of two expressions with
nonzero symbolic terms rejects as unsupported nonlinear arithmetic. Thus
`2*n+1` and `n+n+1` can denote the same size, whereas `n*n` is unsupported even
if a caller later supplies a small concrete `n`.

Subtraction is exact, never wrapping or saturating. The current premises must
establish that the right operand is no greater than the left operand before
normalization proceeds. For example, `n-1` requires a sufficient guard such as
`n >= 1`. An unresolved nonnegativity obligation rejects; substituting a
convenient value later does not repair an invalid generic definition.

Comparisons are `==`, `!=`, `<`, `<=`, `>` and `>=`. Declared premises and static
branch guards extend the current natural constraint context. Callee premises
must follow from that context. Equality of symbolic sizes requires implications
in both directions; equal physical width or failed counterexample search does
not establish type equality.

The implementation uses a bounded exact linear implication procedure based on
rational relaxation of integer constraints. A successful inconsistency check
can establish an obligation. Incomplete search supplies no evidence and an
unresolved required implication rejects. This is not a complete solver for
integer arithmetic.

Mathematical Nat arithmetic has no modular overflow semantics. The current
symbolic implementation stores affine coefficients/constants as signed
128-bit integers and uses checked arithmetic. Concrete selected-source
specialization uses checked unsigned 32-bit naturals. Exceeding either
representation is a capacity failure, not permission to wrap, truncate or
approximate the value. Concrete negative subtraction also rejects.

## Sizes and zero width

`Bits<n>` requires an admitted static natural expression. A closed instance
retains its exact evaluated size and constructor tag. `Bits<0>` is valid as a
type and remains distinct from `Unit`; `Bits<1>` remains distinct from `Bit`.
Concrete emitters have separate supported-interface restrictions.

An ordinary zero-width value has no quantum owner. `Q<Bits<0>>` and `Q<Unit>`
still have linear owner identities. Zero width does not authorize copying,
implicit dropping or phase erasure. Explicit zero-width consumption and
structural Unit maps retain their specified effects and exact action.

## Static branches, folds and termination

An ordinary function block may bind a natural expression with
`static let name = expression;`. The initializer uses the static context and
the same exact natural arithmetic as sizes and fold bounds. It sees preceding
bindings, including an enclosing static parameter or fold index; it cannot
read runtime classical values or quantum owners. Static bindings cannot shadow
another visible lexical binding. Their names end at the containing block and
are unavailable as runtime values.

For example, `static let width = n+n;` supplies a normalized
size to an already checked generic definition:

```qli
static let width = n+n;
identity[width](q)
```

`static let rounds = n+1;`
may supply a fold bound. Within a fold, `static let next = i+1;` is evaluated
for the current index. Definition checking still visits dead arms and empty
fold bodies. A closed instance evaluates aliases with the same checked Nat
evaluator used for generic sizes and fold bounds. Alias storage is charged to
the existing work/storage budgets. Finite lowering erases checked unused
aliases; using a sized operation still requires a supported output profile.

This binding produces no runtime instruction, new owner, operation access or
trusted evidence. It does not introduce public `static fn`/`const fn` builders
or complete static helper or phase-table evaluation.

`if static comparison { ... } else { ... }` checks both original source arms
under their respective premises. After all closed bindings are supplied, the
concrete elaborator evaluates the comparison and elaborates the selected arm.
A constant condition does not hide an unresolved name, invalid owner use or
missing operation access in the other arm.

The current transitional fold spelling is
`for static k in start..end carry pattern = initial { ... yield result; }`.
The range is half-open and must be nonnegative: `end >= start`. The carried
value has the same exact type/tree across iterations. Each iteration receives
its declared carry owners; unrelated live owners cannot be captured as hidden
carry. The final result returns the threaded value. A zero-iteration range
returns the evaluated initial value and still checks the original body for
names, types, ownership and capabilities. No implicit discard implements a
fold exit.

This spelling does not establish the planned `qfor` API. Its replacement and
the distinction from ordinary iteration remain tracked in
[#194](https://github.com/MGYamada/Qleisli/issues/194).

Runtime function self-recursion is admitted only when checked static Nat
arguments do not increase and at least one strictly decreases under the
current guards. A same-size call, absence of a decreasing Nat or an unproved
decrease rejects. Mutual dependency cycles reject. Concrete specialization
also rejects an active repeated specialization identity and applies aggregate
call/depth/work limits. Total classical declarations instead have acyclic
calls and their separate [finite expression grammar](source-text.md#total-classical-declarations).
No general recursion or runtime unbounded loop is introduced.

## Operation repetition and access

`repeat_op(count, U)` is a static operation description, not execution of a
host loop. An ordinary count is a natural expression. The special count form
`2^e` is admitted here with a natural atom exponent; use parentheses for a
compound exponent, for example `2^(n+1)`. It is not a general natural-expression
power operator and cannot be inserted into `Bits<2^n>` by this rule.

The selected concrete path limits the exponent to eight and both each count
and its nested repetition product to 256. Counts and products use checked
arithmetic. A zero count still resolves and checks its provider and required
access. Repetition grants no `Adjoint` or `Controlled` access. The same applies
when a repeated description is forwarded through another generic call.

## Definition checking and concrete capacities

The common original-source judgment checks all declarations, including private
and unused bodies, before a finite or selected-source projection. It checks
static categories, exact type trees, owner/effect rules, generic premises and
capabilities. A concrete instance separately checks complete closed bindings,
actual provider identities, substitutions and supported interfaces. Neither
stage issues a native accepted handle.

The current common judgment has a 1,000,000-unit work allowance. Its selected
profile also limits retained scope storage to 16,384 cells. Natural-expression
depth is limited to 128; type trees have separate 4,096-cell, depth-64 and
64-immediate-field capacities. Accounting units measure implementation work
and retained structures; they are not byte counts or quantum resource bounds.

The current selected-source concrete elaborator limits aggregate function
calls to 1,024, call depth to 16, aggregate fold iterations to 1,024, emitted
source-order steps to 10,000 and charged storage to 100,000 cells. Cache reuse
does not remove call accounting. Separate parser, constraint, lowering, native
and simulation capacities can reject an otherwise meaningful instance.

Capacity failures are reported as limits; invalid types, unsupported syntax or
arithmetic, missing access and non-decreasing cycles retain their own failure
categories. Exhausting a budget is neither acceptance nor proof that a program
has no meaning. Compiler capacities, termination, ownership safety, computed
quantum resources and checked target budgets are distinct obligations.

## Evidence and remaining work

Existing small sized-source regressions cover guarded subtraction and affine
equality, nonlinear refusal, original obligation spans, static dead arms,
empty folds, forwarded premises/access, mutual cycles, complete bindings,
repeat limits and aggregate call/fold/storage accounting. These are bounded
implementation checks, not a theorem of general specialization preservation.

Rust still produces untrusted proposals. The exact resulting artifact and any
independent request pass their native gate as described by the
[production boundary](production-boundary.md). Native validity of that output
does not prove that specialization preserves the original source meaning.
The two admitted QLV1 ownership/scope guarantees retain their original-root
scope; QS, PR, quantitative RS and EXACT remain pending at their broader scopes.

General static helper evaluation, computed phase-table construction and the
remaining public static-language work belong to #63/#28. This chapter supplies
no arbitrary code execution, I/O, randomness, raw IR injection, trusted evidence
constructor or floating-point substitute for an exact obligation. Generic QFT
implementation remains outside the current human-selected goal.
