# Static values, constraints and bounded specialization

A **static computation** is a computation that elaboration performs before
any runtime step. It is deterministic and it terminates. Its result is one of
four things: an admitted size, an exact constant, a closed description of an
operation, or an input to the check of a constraint or of a capability.

A program uses static computations to write one declaration for many sizes
or operations. A function over `Q<Bits<n>>` is such a declaration: its caller
fixes `n` before the program runs.

This chapter specifies the static computations of edition 2026. It covers
static parameters, natural expressions, `requires` clauses, static bindings,
Nat helpers, static branches and folds, operation descriptions, and the
specialization of a generic declaration. The
[type boundary](type-model.md) and the [authority hierarchy](authority.md)
take precedence over this chapter. The chapter does not define a general
compile-time programming language.

Two terms recur in every section:

- The **common judgment** is the check that the checker runs on the original
  source of every declaration. It runs before every concrete elaboration.
- A **closed instance** is a declaration with a concrete value bound to each
  of its static parameters.

The CLI checks source through two [routes](diagnostics.md#routes), the project
route and the selected-entry route. Both run the common judgment. Each
elaborates closed instances within its own limits.

When a program breaks a rule, the common checker reports a class. The rule
names that class in parentheses, as in (`size`). The code `parse` marks a
syntax error. [Codes](diagnostics.md#codes) maps each class to the `code`
that a route reports.

<a id="static-categories-and-binding"></a>

## Static categories

The category of a static value says what the value describes: a size, a
type tree or an operation. A static computation reads the explicit static
environment and the admitted ordinary finite labels. Static values have three
categories.

| Category | Values |
| --- | --- |
| `Nat` | A nonnegative static integer. It is not a runtime integer and not an ordinary `Bit`. |
| `Basis` | An exact finite type tree. |
| `Op<A>` | An **operation description**: a static description of an operation over the tree `A`. |

The explicit [`Op<A -> B>` form](type-model.md#general-pure-operation-arrows)
names an exact input tree and an exact output tree separately. The slot after
its comma holds a Meaning refinement. A **provider** is the operation that a
static argument supplies for an `Op` parameter.

Rules:

- A static computation must not read a live quantum owner, a runtime input or
  the host environment. It has no execution authority.
- Elaboration normalizes or resolves each static result before canonical Core.
- No value of a static category is a live `Q<A>` owner.
- A runtime value, a measurement result or a quantum owner must not determine
  a static size, a provider, a static condition or a loop bound.
- An operation description must satisfy its independent evidence obligations
  and its native acceptance obligations.
- An abstract `Basis` parameter is opaque. Finiteness alone permits no type
  reflection, preparation, tuple decomposition, control or inverse.
  [Generic responsibilities](type-model.md#inference-and-generic-responsibilities)
  give the independent access and specialization rules.
- Belonging to the class of static computations grants a form no syntax and
  no result type. Each form that this chapter specifies keeps its own
  contract.

## Static parameters

```text
StaticParameters ::= "[" StaticParameter ( "," StaticParameter )* "]"
StaticParameter  ::= "const" Identifier ":" StaticKind
StaticKind       ::= "Nat" | "Basis"
                   | "Op" "<" BasisType ( "->" BasisType )? ( "," MeaningName )? ">"
```

A **static parameter** is a compile-time parameter of a declaration. A
declaration takes one for each size, type tree or operation that a caller or
the host chooses before the program runs. The contextual marker `const`
introduces a static parameter, as in `const n: Nat` followed by
`const U: Op<Bits<n>>` in a function header. The **kind** of a static
parameter is the annotation after its colon. At a call, brackets supply the
static arguments and parentheses supply the runtime arguments.

Rules:

- In a parameter header, `const` is not a runtime value, a storage
  declaration or a general compile-time function API. An ordinary function
  or a local named `const` keeps ordinary name resolution.
- Static parameters are explicit, positional and ordered. The kind of a
  parameter may refer only to earlier parameters. For example, `n: Nat` must
  precede `U: Op<Bits<n>>`. A kind that refers to a later parameter is a
  forward kind dependency, and the checker rejects it.
- Two static parameters of one declaration must not share a name (`binding`).
- A source call must supply the complete ordered list of static arguments
  (`static-arity`).
- When the host selects an entry, it must supply the complete set of named
  bindings (`static`).
- The checker infers no missing binding from a matching width or from a
  provider name.
- The checker rejects the marker `static` in a parameter header, and it
  reports the error at that marker (`parse`). This also holds in a header
  that mixes `static` with `const`. The diagnostic tells the author to write
  `const` instead; see [Retired spellings](#retired-spellings). The forms
  `if static`, `qfor static`, `for static` and `static let` keep the word
  `static`.

The checker accepts this declaration, which declares `n` before the kind that
uses it:

```qli
pub unitary fn use_op[const n: Nat, const U: Op<Bits<n>>](q: Q<Bits<n>>) -> Q<Bits<n>> requires Applicable(U) { U(q) }
```

The checker rejects a forward kind dependency:

```qli
pub unitary fn f[const U:Op<Bits<n>>,const n:Nat](q:Q<Bits<n>>)->Q<Bits<n>> requires Applicable(U){U(q)}
```

The checker rejects the marker `static` in a header (`parse`):

```qli
pub fn f[static n:Nat](q:Q<Bit>)->Q<Bit>{q}
```

## Natural expressions and constraints

```text
Natural       ::= NaturalFactor ( ( "+" | "-" ) NaturalFactor )*
NaturalFactor ::= NaturalAtom ( "*" NaturalAtom )*
NaturalAtom   ::= DecimalLiteral | Name | HelperCall | "(" Natural ")"
Comparison    ::= Natural ( "==" | "!=" | "<" | "<=" | ">" | ">=" ) Natural
```

A **natural expression** denotes a static `Nat`. A program writes one where
it states a size, a fold bound or a repetition count, and on each side of a
comparison. A natural expression consists of nonnegative decimal literals,
static Nat names, parentheses, `+`, `-`, `*` and calls of checked acyclic
[Nat helpers](#provisional-bounded-nat-helpers). Multiplication binds more
tightly than addition and subtraction. Operators of one level associate to
the left. A natural expression is not runtime arithmetic.

A **premise** is a comparison that the checker may assume. The
**constraint context** of a program point is the set of premises in force
there.

### Arithmetic

The arithmetic of natural expressions is exact. The common judgment checks
an expression in its symbolic form, before a closed instance supplies
concrete values.

Rules:

- A natural expression must not use division, remainder or arbitrary
  exponentiation. The grammar admits none of them.
- Symbolic normalization turns a natural expression into an exact affine
  expression over the original static binder identities: a constant plus a
  constant multiple of each binder. It folds constants. It accepts
  multiplication by an expression that normalizes to a constant.
- The checker rejects a product of two expressions that each have nonzero
  symbolic terms. Such a product is nonlinear arithmetic (`unsupported`).
  The checker rejects `n*n` even if a caller later supplies a small concrete
  `n`.
- Subtraction is exact. It never wraps and never saturates. Before
  normalization proceeds, the constraint context must establish that the
  right operand is no greater than the left operand (`size`). For example,
  `n-1` requires a guard such as `n >= 1`.
- The checker rejects an expression that leaves a nonnegativity obligation
  unresolved. Substituting a convenient value later does not repair an
  invalid generic definition.
- Nat arithmetic has no modular overflow. A value that exceeds the capacity
  of its representation is a capacity failure (`limit`). The failure gives
  no permission to wrap, truncate or approximate. [Capacities](#capacities)
  states each representation.
- The checker rejects a concrete subtraction with a negative result.

The checker accepts this declaration, because `2*n+1` and `n+n+1` denote the
same size:

```qli
pub unitary fn f[const n: Nat](q: Q<Bits<2*n+1>>) -> Q<Bits<n+n+1>> { q }
```

The checker rejects the nonlinear size (`unsupported`):

```qli
pub unitary fn f[const n: Nat](q: Q<Bits<n*n>>) -> Q<Bits<n*n>> { q }
```

The checker rejects the unguarded subtraction (`size`):

```qli
pub unitary fn f[const n: Nat](q: Q<Bits<n-1>>) -> Q<Bits<n-1>> { q }
```

### Comparisons and the constraint context

A comparison relates two natural expressions. The comparisons are `==`,
`!=`, `<`, `<=`, `>` and `>=`. A program states a comparison as a premise of
a declaration or as the guard of a static branch. The checker then uses the
constraint context to decide whether a required fact follows.

Rules:

- Declared premises and static branch guards extend the constraint context.
- The premises of a callee must follow from the constraint context of the
  call (`size`).
- Two symbolic sizes are equal only when the checker establishes the
  implications in both directions. Equal physical width does not establish
  type equality. A failed search for a counterexample does not establish it
  either.
- The checker rejects a program when it does not establish a required
  implication.

> **Implementation note.** `src/frontend/linear.rs` holds the implication
> procedure. The procedure is bounded, exact and linear, and it relaxes the
> integer constraints to rational ones. A successful inconsistency check
> establishes an obligation. An incomplete search supplies no evidence.
> Ordered binder identities and deterministic collections fix its traversal
> and its tie-breaking. `src/frontend/check/normalize.rs` normalizes natural
> expressions for the common judgment.

## Unified `requires` obligations

```text
RequiresClause      ::= "requires" Requirement ( "," Requirement )*
Requirement         ::= Comparison | CapabilityPredicate
CapabilityPredicate ::= ( "Applicable" | "Adjointable" | "Controllable" ) "(" Identifier ")"
```

A `requires` clause states what a declaration needs from its static
arguments. The checker checks the body under the entries of the clause, and
it checks that each caller establishes them. One comma-separated clause
holds two kinds of entries: numeric entries and capability requirements. A
**numeric entry** is one of the six comparisons. Both kinds use the common
judgment, and both use the substitution checks of a closed instance.

A **capability** is one of the three ways to use the provider of an operation
description: Applicable, Adjointable and Controllable. A
**capability requirement** is one of `Applicable(U)`, `Adjointable(U)` and
`Controllable(U)` in a `requires` clause.

| Capability predicate | Capability |
| --- | --- |
| `Applicable(U)` | Applicable: forward application |
| `Adjointable(U)` | Adjointable: adjoint application |
| `Controllable(U)` | Controllable: controlled application |

A capability requirement describes justified access to the actual provider.
It does not describe the Meaning of the provider or its semantic unitarity.
Those are separate.

Rules:

- A capability requirement must name an operation parameter of its
  declaration. The checker rejects an unknown name (`name`). It rejects a
  parameter of another kind (`access`).
- A clause must not repeat a capability requirement (`access`).
- Each capability is independent. Another capability requirement, an effect
  annotation or a Meaning refinement supplies none.
- The three adjective names are contextual in this clause. They construct no
  operator, and an annotation alone grants no access.
- The checker rejects the spellings `Apply(U)`, `Adjoint(U)` and
  `Controlled(U)` (`parse`). Each diagnostic is located and says how to
  migrate; see [Retired spellings](#retired-spellings).
- A clause must not hold an arbitrary Boolean formula or a user-defined
  constraint predicate. The clause admits no broader const language.

The order of the entries matters, because a numeric entry can guard the
arithmetic of a later entry.

Rules:

- The checker normalizes numeric entries in source order. While it checks the
  arithmetic of an entry, only the preceding numeric entries extend the
  initial Nat context.
- A later guard does not repair an earlier unguarded subtraction. Thus
  `requires n >= 1, n-1 <= 3` is well formed, and the checker rejects
  `requires n-1 <= 3, n >= 1` at `n-1` (`size`).
- A capability requirement between two numeric entries adds no numeric fact
  and removes none.
- After this ordered check, the normalized numeric facts form a conjunction.
  The capability requirements form the explicit capability assumptions of the
  declaration.
- The checker checks the original body under those facts, including both
  static arms and empty fold bodies.

A generic call and a closed instance each discharge the clause of the
declaration that they use.

Rules:

- A generic call substitutes exact static arguments simultaneously. The
  caller context must establish every numeric premise of the callee (`size`)
  and every capability that the callee requires (`access`).
- The checker rejects an unresolved premise or a missing capability at its
  source obligation.
- A closed instance separately evaluates the checked numeric facts. It checks
  the actual providers before the elaboration of the concrete body.
- The checker rejects a false numeric premise (`size`). The diagnostic
  identifies three things: the selected entry or the resolved provider, the
  failed predicate, and the original location of its clause.
- A convenient closed instance does not validate an ill-formed generic
  declaration.
- These obligations compose with opaque `Basis` parameters, exact `Bits<n>`
  sizes and the
  [provider rules](type-model.md#inference-and-generic-responsibilities).
  They introduce no runtime condition, owner conversion, semantic evidence or
  native acceptance rule.

The checker accepts this declaration. The guard `n >= 1` precedes the
subtraction, and `Applicable(U)` permits the application:

```qli
fn step[const n: Nat, const U: Op<Bits<n>>](q: Q<Bits<n>>) -> Q<Bits<n>>
requires n >= 1, Applicable(U), n-1 <= 3 {
    U(q)
}
```

The checker rejects a repeated capability requirement (`access`):

```qli
pub unitary fn f[const U: Op<Bit>](q: Q<Bit>) -> Q<Bit> requires Applicable(U), Applicable(U) { q }
```

The checker rejects a Boolean connective in a clause (`parse`):

```qli
pub unitary fn f[const n:Nat](q:Q<Bit>)->Q<Bit> requires n >= 1 && n <= 2 {q}
```

The checker accepts this declaration. It rejects a closed instance with `n`
equal to 0 at `n >= 1`, and it rejects one with `n` equal to 9 at `n <= 2`
(`size`):

```qli
pub unitary fn bounded[const n:Nat](q:Q<Bits<n>>)->Q<Bits<n>>
        requires n >= 1, n <= 2 {q}
```

## Sizes and zero width

This section states the rules for the size `n` of a type `Bits<n>` and for
types of zero width. A type of zero width holds no qubit. Its quantum owner
is linear all the same.

Rules:

- The size of `Bits<n>` must be an admitted natural expression.
- A closed instance keeps its exact evaluated size and its constructor tag.
- `Bits<0>` is a valid type. It is distinct from `Unit`. `Bits<1>` is distinct
  from `Bit`.
- An ordinary zero-width value has no quantum owner. `Q<Bits<0>>` and
  `Q<Unit>` have linear owner identities.
- Zero width authorizes no copying, no implicit dropping and no phase erasure.
- Explicit zero-width consumption and structural Unit maps keep their
  specified effects and their exact action.

## Static bindings

```text
StaticLet ::= "static" "let" Identifier "=" Natural ";"
```

A **static binding** names a natural expression inside an ordinary function
block, as in `static let name = expression;`. Use one to compute a size or a
bound once and refer to it by name. The initializer uses the static context
and the same exact natural arithmetic as sizes and fold bounds.

Rules:

- The initializer sees the preceding bindings, including an enclosing static
  parameter and an enclosing fold index.
- The initializer must not read a runtime classical value or a quantum owner.
- A static binding must not shadow another visible lexical binding
  (`shadow`).
- The name of a static binding ends at its containing block. A program
  cannot use the name as a runtime value (`type`).
- Definition checking visits a static binding wherever it stands, also in
  dead arms and in empty fold bodies.
- A closed instance evaluates a static binding with the checked Nat evaluator
  that it uses for generic sizes and fold bounds.
- A static binding produces no runtime instruction, owner, operation access
  or trusted evidence.

For example, `static let rounds = n+1;` may supply a fold bound. Within a
fold, `static let next = i+1;` is evaluated for the current index. In the
body below, `static let width = n+n;` supplies a normalized size to a checked
generic definition:

```qli
static let width = n+n;
identity[width](q)
```

The checker accepts this source, which holds that body with one more static
binding:

```qli
pub unitary fn identity[const n:Nat](q:Q<Bits<n>>)->Q<Bits<n>>{q}
pub unitary fn twice[const n:Nat](q:Q<Bits<2*n>>)->Q<Bits<2*n>>{
    static let width=n+n; static let normalized=width+0; identity[normalized](q)
}
```

The checker rejects a static name that is used as a runtime value:

```qli
pub observe fn main()->Bit{static let n=1;n}
```

> **Implementation note.** The storage of a static binding is charged to the
> work and storage budgets of the route. On the project route, finite
> lowering erases a checked static binding that the body does not use.

## Provisional bounded Nat helpers

```text
NatHelper  ::= "static" "fn" Identifier StaticParameters? "(" ")" "->" "Nat"
               RequiresClause? "{" Natural "}"
HelperCall ::= Name ( "[" ( Natural ( "," Natural )* )? "]" )? "(" ")"
```

A **Nat helper** is a first-order static function from `Nat` arguments to a
`Nat` result. A program declares one to name a natural expression that
several sizes, bounds or conditions share.

Rules:

- A helper must have only explicit static `Nat` parameters and no runtime
  parameters (`static`).
- A helper must have the literal result category `Nat` and one
  natural-expression body (`parse`). `Nat` in this position does not become
  an ordinary finite type.
- A helper may call other helpers. The checker accepts a forward reference
  that forms no cycle. Ordinary public and private module visibility applies.
- Two formals of a helper must not share a name (`binding`).
- A helper must not call itself, directly or through other helpers
  (`cycle`).
- The checker checks unused and private helper bodies too.
- A Nat helper is not a runtime entry, an ordinary function or a provider
  (`static`).

A natural expression calls a helper with a complete positional list of
static arguments and an empty list of runtime arguments, as in `twice[n]()`.

Rules:

- A call must supply one argument for each parameter (`static-arity`).
- The common judgment normalizes each helper to an exact affine template over
  its original binder identities. Substitution is simultaneous. A caller
  expression is never rewritten again as a callee parameter.
- The caller must establish every premise of the callee before it uses the
  result (`size`). This holds within a size, another helper, a static
  condition and a fold.
- The refusals of natural arithmetic apply unchanged in a helper and at a
  helper call. They are unproved nonnegativity (`size`), nonlinear arithmetic
  (`unsupported`) and symbolic overflow (`limit`).
- A runtime value, a quantum owner, an operation or a Meaning declaration
  must not supply a helper input. A natural expression must not call one
  (`static`).
- A computed helper result uses the exact size normalization and the
  specialization rules of every other natural expression.

The checker accepts both helpers:

```qli
static fn twice[const n: Nat]() -> Nat { n+n }
static fn previous[const n: Nat]() -> Nat requires n >= 1 { n-1 }
```

The checker rejects a call that does not establish the premise `n >= 1`
(`size`):

```qli
static fn previous[const n:Nat]()->Nat requires n>=1 {n-1} pub observe fn main()->Bit{static let n=previous[0]();0}
```

The checker rejects a dependency cycle (`cycle`):

```qli
static fn first()->Nat{second()} static fn second()->Nat{first()} pub observe fn main()->Bit{0}
```

A helper can index an exact phase schedule. The helper
`static fn exponent[const stage: Nat]() -> Nat { stage+1 }` supplies
`phase[1, exponent[i]()]` inside a bounded fold. Its result is an exact
denominator exponent. It is not a floating-point angle and not a runtime
table.

> **Implementation note.** The selected-entry route keeps the checked
> templates. They are shared and immutable. The route does not expand a call
> graph into duplicate runtime code. One concrete Nat evaluator serves sizes,
> static bindings and fold bounds. It also evaluates the arguments of a
> helper call and the normalized affine result of the call.
> `natural` in `src/frontend/specialize/elaborate.rs` is that evaluator on the
> selected-entry route, and `src/frontend/compile/naturals.rs` holds the one
> of the project route. Template preparation consumes the budget of the
> common judgment. [Capacities](#capacities) states the arithmetic widths and
> the allowances.

## Static branches, folds and termination

### Static branches

```text
StaticIf ::= "if" "static" Comparison Block "else" Block
```

A **static branch** `if static comparison { ... } else { ... }` selects one
of two arms by a comparison of natural expressions. Use one when the body of
a generic declaration depends on a size, as in a separate arm for
`n == 0`.

Rules:

- The checker checks both original source arms, each under its own premise.
- After a closed instance supplies all bindings, the concrete elaborator
  evaluates the comparison and elaborates the selected arm.
- A constant condition hides nothing in the other arm. The checker rejects
  an unresolved name (`name`), an invalid owner use (`ownership`) and a
  missing capability (`access`) in an arm that the condition never selects.

Each line below is a separate source. The checker rejects both, although the
condition selects the first arm. The first has an unknown name (`name`), and
the second uses an owner twice (`ownership`):

```qli
pub unitary fn f(q: Q<Bit>) -> Q<Bit> { if static 0 == 0 { q } else { missing(q) } }
pub unitary fn f(q: Q<Bit>) -> Q<Bit> { if static 0 == 0 { q } else { (q,q) } }
```

### Static folds

```text
StaticFold ::= ( "for" | "qfor" ) "static" Identifier "in" Natural ".." Natural
               "carry" Pattern "=" Expr "{" Statement* "yield" ( Expr ";"? )? "}"
```

A **static fold** threads a value through a finite range of indices. Use one
to repeat a body a static number of times, where each iteration hands its
result to the next. The **carry** is the value that the fold threads. The
fold over quantum owners is spelled
`qfor static k in start..end carry pattern = initial { ... yield result; }`.
The fold over ordinary values is spelled `for static`, with the same header
and tail. `yield` supplies the next carry. A `yield` without an expression
supplies `()`.

The carry decides the spelling of a fold.

Rules:

- The carry of `qfor static` must contain at least one quantum owner
  (`type`). A zero-width `Q<Unit>` owner counts. A product of ordinary and
  quantum values is permitted.
- The carry of `for static` must be ordinary. The checker rejects a quantum
  carry there (`type`). The diagnostic is located and suggests
  `qfor static`.
- The
  [control boundary diagnostic](source-text.md#diagnostics-at-control-boundaries)
  identifies both carry mismatches and names the corresponding fold syntax.
- The checker rejects `qfor` without the marker `static` (`parse`).
- A fold body must end with `yield`, also for an empty range (`parse`).

The range of a fold is static.

Rules:

- The range is half-open and must be nonnegative. The constraint context
  must establish `end >= start` (`size`).
- A bound must not depend on runtime classical data or on a measurement
  outcome. A fold has no runtime bound.
- A closed instance evaluates the bounds of each fold with the common checked
  evaluator of natural expressions. The specialization capacity and the work
  capacity of its route apply.

A fold threads its carry explicitly.

Rules:

- The initializer is evaluated once.
- The carried value has the same exact type tree in every iteration
  (`type`). A fold converts no carry shape.
- Each iteration receives its declared carry owners. The body must not
  capture an unrelated live owner as hidden carry (`ownership`).
- A quantum owner outside the carry stays in the caller frame. The body must
  not access it.
- Both arms of a branch in the body must preserve the required owner
  interface and the carry tree.
- The fold returns the threaded value. A range of zero iterations returns the
  evaluated initial value.
- The checker checks the original body for names, types, ownership and
  capabilities, also for a range of zero iterations.
- A fold exit discards nothing implicitly. A fold captures and discards no
  quantum owner implicitly.
- The operations of the body keep the ordinary effect rules and capability
  rules. The fold syntax grants no inverse access and no control access.

Each line below is a separate source. The checker accepts both. The second
returns `1`:

```qli
use std::gate::x; pub unitary fn f[const n:Nat](q:Q<Bit>)->Q<Bit>{qfor static i in 0..n carry a=q{yield x(a);}}
pub observe fn main()->Bit{for static i in 0..3 carry a=0{yield not a;}}
```

Each line below is a separate source, and the checker rejects each. In order,
they have a quantum carry in `for static` (`type`), an ordinary carry in
`qfor static` (`type`), no marker `static` (`parse`), no `yield` (`parse`)
and a hidden capture of `r` (`ownership`):

```qli
pub unitary fn f(q:Q<Bit>)->Q<Bit>{for static i in 0..0 carry a=q{yield a;}}
pub observe fn main()->Bit{qfor static i in 0..0 carry a=0{yield a;}}
pub unitary fn f(q:Q<Bit>)->Q<Bit>{qfor i in 0..1 carry a=q{yield a;}}
pub unitary fn f(q:Q<Bit>)->Q<Bit>{qfor static i in 0..0 carry a=q{a}}
pub unitary fn f(q:Q<Bit>,r:Q<Bit>)->(Q<Bit>,Q<Bit>){let q=qfor static i in 0..0 carry a=q{yield r;};(q,r)}
```

> **Implementation note.** Both spellings lower through one fold
> representation to proposed raw or hierarchical IR. Independent native
> checking then applies. On the project route,
> `src/frontend/compile/lower/statics.rs` selects the arms and unrolls the
> folds.

### Termination of calls

This section states the rules for a function that calls itself, directly or
through other functions. A runtime function may call itself only under a
checked decrease of its static `Nat` arguments.

Rules:

- In a self-call, no checked static `Nat` argument may increase, and at least
  one must strictly decrease under the guards in force (`cycle`). The checker
  rejects a self-call in three cases: the call has the same size, no `Nat`
  argument decreases, or the checker cannot prove the decrease.
- The checker rejects a cycle of mutual dependencies (`cycle`).
- Concrete specialization rejects a specialization identity that is already
  active (`cycle`). It applies the aggregate call, depth and work limits
  (`limit`).
- A total classical declaration has acyclic calls and its separate
  [finite expression grammar](source-text.md#total-classical-declarations).
- The language has no general recursion and no unbounded runtime loop.

The checker accepts this declaration. The arm that holds the self-call has
the premise `n != 0`, which guards `n-1` and proves the decrease:

```qli
pub unitary fn f[const n: Nat](q: Q<Bit>) -> Q<Bit> { if static n == 0 { q } else { f[n-1](q) } }
```

The checker rejects a self-call of the same size (`cycle`):

```qli
pub unitary fn f[const n: Nat](q: Q<Bits<n>>) -> Q<Bits<n>> { f[n](q) }
```

## Finite runtime control and resources

This section describes how each control form bounds the execution of a
program. For each closed instance, the admitted control forms describe a
finite execution structure. The rules of this section apply together with
the type, effect, owner, provider and concrete-profile checks. They enable
no form that a route refuses.

### Control forms

| Form | Termination and resource structure |
| --- | --- |
| Ordinary `if` | The program evaluates an ordinary `Bit` condition and executes one finite arm per history. Both original arms must check, and both must return the same complete result and the same live-owner interface. A choice that depends on a measurement retains every complete history and its weight. |
| `if static` | The checker checks both original arms, each under its own premise. Elaboration then selects the arm that the closed static comparison determines. The unselected arm cannot hide a source obligation. |
| `for static` and `qfor static` | The fold evaluates its initializer once, then threads the exact carry through the finite half-open range. A zero range returns that initializer, and the checker checks the original body all the same. A bound cannot depend on runtime classical data or on measurement outcomes. |
| `power(U, count)` | The application applies the checked provider a finite, static number of times. The count capacity and the materialization capacity apply. The runtime input is evaluated once. A zero count checks the original provider, its Meaning and the requested capability. |
| Ordinary calls | A call follows the checked dependency rules and the static-specialization rules above. A direct self-call requires that no static `Nat` argument increases and that at least one has a proved strict decrease. The checker rejects mutual cycles and general recursion. Concrete expansion also enforces its call, depth and work capacities. |
| Coherent `qif` and controlled operation descriptions | These forms use finite provider bodies. Each body has its independently checked controlled access and its ordered interfaces. The sectors of a coherent selector are not ordinary alternative execution histories. Execution preserves their relative phase and the controlled action. |
| Ordinary `match` | The program selects one arm among the exhaustive, disjoint arms of an ordinary enum value. A `match` has at most 64 arms. [Parsed finite type declarations](source-text.md#parsed-finite-type-declarations) specifies the form. |
| Coherent `qmatch` | The form applies one checked arm for each exact label of a quantum selector. It does not measure the selector. A `qmatch` has at most 64 arms. [Exact-label coherent selection](source-text.md#exact-label-coherent-selection) specifies the form. |

This chapter specifies neither `match` nor `qmatch`. Each form executes in
the bounded profiles that its own section states, within the native-transport
boundaries of that section. The rules of this section neither widen nor
narrow those profiles.

### Owners in branches and iterations

The rules below say how a branch and an iteration treat quantum owners.

Rules:

- Each branch and each iteration must respect its complete declared owner
  interface and the surrounding caller frame. This includes zero-width owners
  and correlations with an external reference.
- Declared consumption and fresh returned owners keep their operation
  contracts.
- Internal workspace must satisfy its declared consumption contract or its
  declared return contract.
- An empty fold, an unselected arm or a successful measurement result grants
  no implicit discard, reset or clean release.
- Exact clean release keeps its all-input, reference-safe zero-return
  obligation.
- These rules also apply when a finite body contains further branches, folds
  or calls.

### Work and storage bounds

The rules below say how a bound on work or on storage composes across the
control forms. A **per-history work measure** is an additive measure of the
work of one execution along one history.

Rules:

- For a per-history work measure, the bound of a sequence is the sum of the
  bounds of its parts.
- The bound of a finite fold is the finite sum of the bounds of its
  iterations.
- The bound of an ordinary conditional is the overhead of its condition and
  its merge, plus the maximum of the bounds of its arms.
- These are composition rules for a declared measure. They are not target
  costs inferred from source spelling.
- Whole-ensemble evaluation and checking may process both arms and all
  histories. They require their own bounds.
- The resource cost of coherent control must account for the controlled
  implementation that realizes it. Neither the cheaper sector nor the
  ordinary conditional rule on the two source arms gives that cost.
- Peak live storage follows the lifetimes of owners and workspace, including
  the caller frame. A sum of separate peaks gives only a conservative upper
  bound.
- Resource Safety can quantify over this finite structure for the specified
  closed instance.
- A quantitative claim must bind the artifact, the target, the measures, the
  schedule and the checked bounds that the
  [realization contract](realization.md#quantitative-resource-claims)
  requires.
- Three things are distinct: source-level summaries, the capacities of the
  compiler and the checker, and target resource certificates.
- Finiteness alone proves neither a particular target budget nor the
  correspondence of source and target resources.

### Loops, recursion and retry

This section names the forms of repetition that the core language does not
have. A **repeat-until-success (RUS)** construct would repeat a quantum trial
until a measured success. The core has none.

Rules:

- The core has no runtime-counted loop, no unbounded `while`, no general or
  mutual recursion, and no source-level retry or RUS construct.
- A measurement outcome must not supply a fold bound. It must not replace the
  checked static decrease of a self-call.
- A specialization whose static `Nat` argument decreases is not recursion on
  a measured runtime value.
- A bounded unrolling may return a success `Bit` together with its declared
  owners only while it retains both the success outcome and the failure
  outcome in the complete instrument.
- A bounded unrolling must not keep only favorable outcomes, and it must not
  normalize them into a successful operation. The
  [postselection boundary](source-text.md#observation-and-postselection)
  applies.
- The bounded host trial driver is separate. It retains no quantum state,
  requires fresh quantum trials, and reports retries, exhaustion and
  execution errors.
- The driver bounds the number of its callbacks. That bound does not bound
  the running time of an arbitrary callback. It gives no permission for a
  source-level quantum retry loop.

An RUS extension would require a separate contract for termination and
resources. That contract must state the success and failure semantics, and
the owners and the workspace on every exit. It must state the composition
with arbitrary references, and the meaning of exhaustion or of a resource
failure. It must distinguish a hard finite bound from an expected cost and
from a probabilistic tail claim. It must supply the evidence that the
requested guarantee needs. Almost-sure termination alone grants neither a
core construct nor a worst-case resource bound. This chapter introduces no
RUS API and no acceptance path.

## Operation repetition and access

```text
OperationDescription ::= Name ( "[" StaticArguments? "]" )?
                       | "adjoint" "(" OperationDescription ")"
                       | "controlled" "(" OperationDescription ")"
                       | "power" "(" OperationDescription "," Count ")"
                       | ( "then_op" | "tensor_op" | "conjugate_op" )
                         "(" OperationDescription "," OperationDescription ")"
                       | "checked_op" "(" Name "," Name ")"
StaticArguments      ::= StaticArgument ( "," StaticArgument )*
StaticArgument       ::= OperationDescription | Natural | "type" "(" BasisType ")"
Count                ::= Natural | "2" "^" NaturalAtom
```

A program builds an operation description from a name and from constructors
such as `adjoint(U)` and `power(U,n)`. It then passes the description as a
static argument or applies it to runtime arguments. This section specifies
the capabilities of each operation description and the three forms that
apply a description to runtime arguments. The
[`requires` clause](#unified-requires-obligations) defines a capability and
the capability requirements `Applicable(U)`, `Adjointable(U)` and
`Controllable(U)`.

### Capability derivation for enabled descriptions

A constructed description has the capabilities that its operands give it.
The table below states them for each constructor.

Write the available capabilities of a well-kinded operation description `U`
as `caps(U) = (A_U, J_U, C_U)`: Applicable, Adjointable and Controllable, in
that order. Each of the three is true or false. The sign `∧` means "and".

Write `U: A -> B` and `V: C -> D`, where each letter is an exact basis tree.
The **ports** of a description are its input tree and its output tree. The
constructor rules below also apply to the `Op<A>` abbreviation, where both
ports are `A`.

| Description | Input → output and required equalities | Derived capabilities `(Applicable, Adjointable, Controllable)` |
| --- | --- | --- |
| `adjoint(U)` | `B -> A` | `(J_U, A_U, C_U)`; constructing it additionally requires `J_U`, even if unused |
| `controlled(U)` | `(Bit,A) -> (Bit,A)`, requiring `A = B` | `(C_U, C_U, C_U)` |
| `power(U,n)` | `A -> A`, requiring `A = B` | `(A_U, J_U, C_U)`, including `n = 0` |
| `then_op(U,V)` | `A -> D`, requiring `B = C` | `(A_U ∧ A_V, J_U ∧ J_V, C_U ∧ C_V)` |
| `tensor_op(U,V)` | `(A,C) -> (B,D)` in that axis order | `(A_U ∧ A_V, J_U ∧ J_V, C_U ∧ C_V)` |
| `conjugate_op(U,V)` | `B -> B`, requiring `C = D = A` | `(A_U ∧ J_U ∧ A_V, A_U ∧ J_U ∧ J_V, A_U ∧ J_U ∧ C_V)` |
| `checked_op(U,M)` | `A -> B`, matching both M ports | The capabilities of U, unchanged. The description keeps its separate obligation of exact Meaning equality. |

Rules:

- A capability is a fact that source checking establishes about an
  implementation path. It is untrusted. It is not a proof of mathematical
  unitarity or of native acceptance.
- An opaque operation parameter has exactly the capabilities that its
  `requires` clause declares. Neither its `Op<A>` kind nor a Meaning
  refinement adds a capability.
- The checker checks every operand and every count before it uses the table.
- A short circuit erases none of these errors: a missing provider, an invalid
  count, a false Meaning or a missing requested capability. A zero power and
  an unused declaration are no exceptions.
- A description may have no capability. The checker rejects a program that
  forwards such a description to a parameter that requires a capability
  (`access`).
- Forming `controlled(U)` gives no direct application access and no adjoint
  access to the original opaque `U`.

The `controlled` row reflects the supported construction of a transparent
controlled circuit. The retained circuit can itself be applied, reversed or
controlled. This is a capability of the constructed object. It is not a rule
that every mathematically unitary black box supplies those implementations.

`conjugate_op(U,V)` denotes `U V U†` in column-vector order. Its Controllable
capability needs the Applicable and Adjointable capabilities of `U` and the
Controllable capability of `V`. The controlled realization places the forward
and adjoint circuit paths of `U` around the controlled circuit path of `V`.
It requires no controlled `U`. The exact phase and the identity on the
inactive branch are retained. They are not inferred from channel equality.

### Source providers and language primitives

An operation can be an ordinary function, a language primitive or an
external artifact. This section states which of them serve as providers and
which capabilities a source provider has.

A **source provider** is an ordinary function that serves as a provider. It
is transparent: the checker has its body. A **language primitive** is an
operation that the language supplies under a bare spelling, such as `h`. The
[primitive boundary](primitive-boundary.md) lists the language primitives.

Rules:

- A source provider must have the exact quantum interface. The checker checks
  all its instantiated premises.
- General pure application permits a provider whose effect, as its callers
  see it, is at most Isometry.
- Reverse access also requires that the effect callers see is Unitary, and
  it requires usable inverse evidence.
- Control also requires equal exact ports.
- Under the
  [public-effect rule](source-text.md#ordinary-function-effects-and-assertions),
  the checked public effect governs external callers and the public
  providers that the host selects. Calls within one module keep the internal
  inference, which is checked independently.
- The checker checks eligibility before specialization, inlining or cache
  reuse. The body and the artifact undergo their separate checks.
- Take a source provider whose callers see a Unitary effect, with operation
  actuals `U_i`. The conservative common rule gives it the capabilities
  `(true, ∧_i(A_i ∧ J_i), ∧_i(A_i ∧ J_i ∧ C_i))`. The rule includes unused
  operation actuals. It makes no claim of maximal inference.
- With no operation actuals, the rule gives the Applicable and Adjointable
  capabilities, plus the Controllable capability for equal ports.
- The declared premises of the provider apply before this rule. The value
  `true` cannot bypass a missing required capability.

A language primitive and an external artifact are not source providers.

Rules:

- A language primitive uses its exact interface and its materializable
  circuit paths where the direct application grammar permits it.
- A name in a static operation argument must be an ordinary function or an
  operation parameter. The checker rejects a language primitive in that
  position (`type`). It does not wrap a primitive name into a source
  provider.
- An external artifact cannot declare its own trusted capability set.
- Closed materialization needs three things: the supported retained
  implementation, the exact source and dependency identity, and fresh native
  evidence. The checker rejects an unsupported external provider.

A capability is a source-checking fact.

Rules:

- An inferred capability, a successful common judgment or a named Meaning is
  never an executable receipt.
- The admitted
  [general arrow rules](type-model.md#general-pure-operation-arrows) admit no
  other form of the retired
  [operations design packet](../design/operations.md).

<a id="application-and-repetition-profiles"></a>

### Controlled application

```text
ControlledApplication ::= "controlled" "(" OperationDescription ")" "(" Expr "," Expr ")"
```

The canonical controlled application is `controlled(U)(c, q)`. It applies
the description `U` to the target `q` under the control `c`. The control is
a quantum owner, and the application returns it together with the target.

Rules:

- The runtime arguments are evaluated once, the control first and the target
  second.
- The control must have the exact type `Q<Bit>`. The target must have the
  exact `Q<A>` type of the operation.
- The result is `(Q<Bit>, Q<A>)`. It keeps both logical owners, also when `A`
  has zero width.
- The application requires the Controllable capability (`access`), also in
  an unused body and for a zero power.
- The checker rejects an ordinary classical `Bit` as control. It rejects one
  owner in both argument positions. It rejects a number of arguments other
  than two (`arity`).
- The control is the first, low axis. The exact phase is retained.
- A single-stage ordinary call `controlled(q)` keeps normal name resolution.

Each line below is a separate source. The checker accepts the first, where
`z` is `std::gate::z`. It rejects the second, which declares only
`Applicable(U)` (`access`):

```qli
unitary fn f(c:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){controlled(power(z,0))(c,q)}
unitary fn unused[const U:Op<Bit>](c:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>) requires Applicable(U){controlled(power(U,0))(c,q)}
```

### Adjoint application

```text
AdjointApplication ::= "adjoint" "(" OperationDescription ")" "(" Expr ")"
```

The canonical unary adjoint application is `adjoint(U)(q)`. A program uses
it to apply an operation in reverse, as the example below undoes `h`. The
application has two stages. The first stage holds a static operation
description. The second stage evaluates one runtime input. The adjoint of a
unitary equals its inverse. The adjoint of an isometry need not be a
two-sided inverse.

Rules:

- The application requires the Adjointable capability of the actual
  operation (`access`) and an exact quantum-owner interface.
- Unitarity alone grants no access. A Meaning annotation alone grants none.
- The same checks apply in an unused body and to a zero-count description.
- The two stages construct no runtime callable and infer no Adjointable
  capability.
- A zero power checks the original provider, its Meaning and the requested
  capability. It evaluates its runtime input once.
- The independent native evidence gates apply.
- `inverse` is not a keyword. An ordinary call `inverse(q)`, a function named
  `inverse` and a local named `inverse` keep normal name resolution.
- The checker rejects the two-stage form `inverse(U)(q)` (`parse`). The
  diagnostic suggests `adjoint(U)(q)`. The language has no inverse API. Such
  an API would require the two-sided inverse law.

The checker accepts this program. `inverse` is an ordinary function, and
`adjoint(oracle)(q)` undoes `h`:

```qli
use std::state::init0;
unitary fn inverse(q:Q<Bit>)->Q<Bit>{q}
unitary fn oracle(q:Q<Bit>)->Q<Bit>{h(q)}
unitary fn undo(q:Q<Bit>)->Q<Bit>{adjoint(oracle)(q)}
pub observe fn main()->Bit{measure_z(h(undo(inverse(init0()))))}
```

The checker rejects this declaration, which declares only `Applicable(U)`
(`access`):

```qli
pub unitary fn bad[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){adjoint(U)(q)}
```

### Descriptions as static arguments

The constructors also build descriptions inside the brackets of a call.
There a constructor applies nothing: it describes an operation that the
callee receives as a static argument.

Rules:

- In a static operation argument, `adjoint(U)` and `controlled(U)` construct
  the corresponding descriptions, also when nested.
- A constructed description keeps the capability derivations that are bound
  to its provider. It also keeps the restrictions of the concrete profile.

### Repetition

```text
PowerApplication ::= "power" "(" OperationDescription "," Count ")" "(" Expr ")"
```

The canonical repetition description is `power(U, count)`. It describes the
operation `U` applied `count` times. The operation comes first and the count
second. Its forward runtime application is `power(U, count)(q)`. Repetition
is not the execution of a host loop.

Rules:

- The original-source syntax tree keeps the complete description, the count
  and the byte spans. No generated function name and no anonymous source loop
  replaces the application.
- The runtime argument is evaluated once, also for a zero count.
- The application requires the Applicable capability (`access`), also for a
  zero count and in an unused body.
- A zero count resolves and checks its provider and the required capability.
- Repetition grants no `Adjointable` capability and no `Controllable`
  capability. This also holds when another generic call forwards a repeated
  description.
- `controlled(power(U, count))(c, q)` and `adjoint(power(U, count))(q)` keep
  the complete repeated provider. Each requires the capability of its outer
  constructor.

The count of a repetition is static.

Rules:

- An ordinary count is a natural expression.
- The count form `2^e` takes a natural atom as exponent. A compound exponent
  needs parentheses, as in `2^(n+1)`.
- `2^e` is not a general power operator of natural expressions. This rule
  does not admit it in `Bits<2^n>`.
- Counts and products of counts use checked arithmetic.
  [Limits of the routes](#limits-of-the-routes) states the largest counts.

The direct form `power(name, literal)(q)` names its operand and gives its
count as a literal.

Rules:

- The literal must be in `0..=4096`, also in an unused body (`limit`).
- For an ordinary function, the direct form uses the runtime group judgment
  over the complete group of quantum inputs.
- For an operation parameter, the direct form uses the opaque basis rule and
  requires the Applicable capability.
- For a language primitive, the direct form checks the exact single-owner
  basis and the Unitary effect.
- A symbolic count or a compound count uses the general operation-provider
  rules and the closed-binding rules.

The word `power` is contextual.

Rules:

- Only an unqualified two-stage `power(...)(...)` denotes the runtime
  application.
- An ordinary single-stage call `power(a, b)`, a declaration named `power`
  and a module import keep normal resolution.
- A root-qualified ordinary reference or call follows the common
  [module lookup](prelude.md). Qualification does not select the runtime
  constructor.
- A static operation argument interprets `power` as the constructor.

The checker accepts this program. It returns `1`, because the argument
`x(init0())` is evaluated once and the zero power applies `oracle` no times:

```qli
use std::gate::x; use std::state::init0;  unitary fn oracle(q:Q<Bit>)->Q<Bit>{x(q)} pub observe fn main()->Bit{measure_z(power(oracle,0)(x(init0())))}
```

The checker rejects a literal count above 4096 (`limit`):

```qli
use std::gate::x; unitary fn oracle(q:Q<Bit>)->Q<Bit>{x(q)} pub unitary fn f(q:Q<Bit>)->Q<Bit>{power(oracle,4097)(q)}
```

The project route rejects the same count inside an outer zero power
(`limit`):

```qli
unitary fn target[const n:Nat](q:Q<Bit>)->Q<Bit>{q}
unitary fn unused[const n:Nat](q:Q<Bit>)->Q<Bit>{power(power(target[1],4097),0)(q)}
```

The checker accepts the count `2^(n+1)` in this declaration. It rejects the
counts `2^n+1` and `3^n` in its place (`parse`), and the count `n*n`
(`unsupported`):

```qli
pub unitary fn f[const n: Nat, const U: Op<Bits<n>>](c: Q<Bit>,q: Q<Bits<n>>) -> (Q<Bit>,Q<Bits<n>>) requires Controllable(U) { controlled(power(U,2^(n+1)))(c,q) }
```

The direct form accepts a language primitive, as in `power(h,0)(q)`. The
three descriptions below require a provider under the ordinary checked
provider contract. Each line is the body of a separate function, where `c`
and `q` are `Q<Bit>` owners and `use_op` has the static parameter
`U: Op<Bit>`. The checker rejects each body, because the language primitive
`h` is not a provider (`type`):

```qli
use_op[power(h,0)](q)
controlled(power(h,0))(c,q)
adjoint(power(h,0))(q)
```

An ordinary function is a provider in the same positions. The checker accepts
each body below. `had` is the ordinary function
`unitary fn had(q:Q<Bit>)->Q<Bit>{h(q)}`, which wraps `h`, and `z` is the
ordinary standard-library function `std::gate::z`:

```qli
use_op[power(had,0)](q)
controlled(power(z,0))(c,q)
adjoint(power(z,0))(q)
```

<a id="definition-checking-and-concrete-capacities"></a>

## Definition checking and closed instances

Checking has two stages. The common judgment checks every declaration in its
generic form. A route then checks each closed instance that it elaborates.

Rules:

- The common judgment checks every declaration, including private and unused
  bodies, before either route elaborates a closed instance.
- The common judgment checks static categories, exact type trees, owner and
  effect rules, generic premises and capabilities.
- A closed instance separately checks four things: its complete closed
  bindings, the identities of its actual providers, its substitutions and
  its supported interfaces.
- Neither stage issues a native accepted handle.
- The checker reports a capacity failure as a limit (`limit`). It does not
  report these failures as limits: an invalid type, an unsupported syntax or
  arithmetic form, a missing capability and a non-decreasing cycle. Each
  keeps its own class.

### Retained source plans

A **plan** is the record that the common judgment keeps of one static call or
of one evidence obligation.

Rules:

- A plan is source metadata. It is not independently checked evidence.
- Keeping a plan discharges no generic obligation that is not yet
  materialized, and it widens no concrete profile.

> **Implementation note.** `src/frontend/check/plans.rs` holds the plans. The
> common judgment keeps each plan under the identity of its original
> structural occurrence. A plan keeps the resolved callee and formal
> identities, the ordered Basis, Nat and Op actuals, and both operation
> ports. It also keeps the Meaning requests, the lexical static bindings, and
> the predicate and fold regions. The plans consume the preparation budget.
>
> The plan of an ordinary natural expression keeps the original arithmetic
> beside the normalized facts, so the concrete checks of intermediate
> overflow and of work apply to it. The plan of a helper call keeps the
> original arguments and the shared checked affine template, under the
> template and result widths that [Capacities](#capacities) states. A zero
> power keeps its child operation and its requests.

### Uninstantiated bodies

A body is **dormant** when no closed instance instantiates its declaration.
Such a body can hold parts whose static values are all closed. On the
project route, a dormant pass checks the closed parts of dormant bodies. A
check that the pass defers stays conditional.

Rules:

- The pass checks each available closed Meaning request and each closed
  static actual in a dormant body. It keeps the original Basis, Nat and Op
  scope.
- The pass visits both siblings of a description, also when one depends on
  an unbound formal. It keeps zero-count children.
- Each concrete actual passes the ordinary exact-port gate, the phase-fixed
  Meaning gate and the requested-access gate.
- When every actual is closed, the concrete body reaches ordinary lowering
  and native checking under its complete instance identity. A
  declaration-only ordinary-root cache does not stand in for that check.
- A Meaning comparison does not itself request every capability in the
  available-access summary of the source.
- An unbound original Op formal stays conditional, also inside
  `checked_op(U,M)`. That deferral does not establish the requested Meaning.
- An unbound actual stays conditional. Its closed siblings undergo their own
  contract checks.
- An obligation of a runtime expression requires its corresponding concrete
  gate.
- In a provably inactive region, a premise that depends on a `Nat` may stay
  conditional. An independently closed sibling cannot be deferred. A fixed
  owner, Meaning or access mismatch cannot be deferred.
- Caller-frame obligations and clean-workspace obligations keep their
  separate scopes.

When part of a description is deferred, a requested capability also reaches
each maximal closed fragment of that description. The table states the
requests that reach the operands of each constructor:

| Description | Requests that reach its operands |
| --- | --- |
| `then_op(U,V)`, `tensor_op(U,V)` | The requested capability, on both operands |
| `adjoint(U)` | A request for Applicable becomes a request for Adjointable, and a request for Adjointable becomes one for Applicable. The construction keeps its required Adjointable capability. |
| `controlled(U)` | The Controllable capability of the child, for each requested capability |
| `conjugate_op(U,V)` | The Applicable and Adjointable capabilities of the outer operand `U`, and the requested capability of the inner operand `V` |
| `power(U,n)` | The requested capability, also at a zero count |

Rules:

- The concrete access gates and their circuit and step limits apply to a
  fragment.
- A check of a fragment does not establish the contract of the whole
  deferred description. It does not replace the aggregate checks that apply
  when all actuals close.

The project route also checks a dormant whole-owner `ctrl` call to a
declaration with closed static actuals.

Rules:

- The project route binds the original expression and its operands to the
  checked plan of the call. It requires that the original effect that
  callers see is Unitary. It preserves the complete ordered interface of
  Q owners.
- The project route independently checks the concrete callee body. It
  submits the Raw ports and the body to the native sector gate.
- Unitarity alone does not establish the sector condition.
- A zero-width Ctrl owner keeps its exact type. It causes a native request,
  although its set of physical axes is empty.
- The control-request capacity applies to this explicit request. Ordinary
  calls keep their separate finite profile.

> **Implementation note.** `src/frontend/compile/dormant.rs` holds the
> dormant pass, and `src/frontend/compile/dormant/controls.rs` checks dormant
> `ctrl` sites. The pass borrows the original operation occurrences. The
> finite adapter of the project route binds complete Basis,
> Nat and Op instances. It checks closed bodies and dormant operation roots,
> and it submits concrete Ctrl calls through the native sector gate.

### Specialization identity and reuse

Two uses of an operation description can share one specialized body. The
**specialization identity** of an operation description decides whether two
uses are the same specialization. It consists of these parts:

- both exact ports, the phase and the source effect;
- the capabilities, the constructors and the ordered children;
- the repetition counts and the issued native dependency identities.

On the project route, a specialization may reuse a retained body.

Rules:

- An ordinary runtime call binds its borrowed plan to the exact original
  expression, the callee and the ordered slices of static and runtime
  operands. A cloned syntax tree of the same shape is not an original
  occurrence.
- Two operation descriptions are one specialization only when their
  specialization identities agree. A zero power keeps the identity of its
  child. Matching matrices alone do not identify two descriptions.
- Every reuse repeats the original checks of actuals, interface and access.
  It also runs a fresh native check of the retained immutable body before it
  copies the action of that body.
- A refused comparison is not a cache miss.
- Entry into a body and failure of a body restore the original instance, the
  static environment and the caller context. Issued identities and charged
  work do not rewind.

Prepared bodies are separate for each consumer and for each representation.

Rules:

- Evidence preparation and selected typed lowering keep separate prepared
  bodies and providers for one original specialization.
- Reuse of a nongeneric provider also keeps the Raw, ordinary or runtime root
  representation. Identical Raw instructions do not identify different
  native request data or view data.
- Each representation undergoes its original checks. Reuse within one
  representation requires the complete accepted artifact to match.

> **Implementation note.** The distinct-specialization counter of the project
> route compares specialization identities within its shared work budget. The
> same identity keys the private registry of bodies and providers in
> `src/frontend/compile/instances.rs`.

## Retired spellings

The table lists the spellings that the language has retired, each with the
form to write instead. The parser rejects each retired spelling at its
marker, predicate or constructor token (`parse`). The diagnostic names the
replacement.

| Retired spelling | Replacement |
| --- | --- |
| `[static name: Kind]` in a parameter header | `[const name: Kind]` |
| `Apply(U)`, `Adjoint(U)`, `Controlled(U)` | `Applicable(U)`, `Adjointable(U)`, `Controllable(U)` |
| `adjoint(U,q)` | `adjoint(U)(q)` |
| `inverse(U)(q)` | `adjoint(U)(q)` |
| `inverse_op(U)` | `adjoint(U)` |
| `controlled_op(U)` | `controlled(U)` |
| `repeat_op(count, U)` | `power(U, count)` |
| `repeat_static(count, U, q)` | `power(U, count)(q)` |

Rules:

- The parser has no legacy header mode.
- To migrate a parameter header, replace each marker and preserve the order
  of the parameters, their kinds and the explicit arguments.

<a id="evidence-and-remaining-work"></a>

## Status and limits

### Capacities

The checker and the routes work within fixed capacities. The table states
each capacity, its limit and where it applies. Accounting units measure
implementation work and retained structures. They are not byte counts and
not quantum resource bounds.

| Capacity | Limit | Scope |
| --- | --- | --- |
| Work of the common judgment | 1,000,000 units | Both routes |
| Retained scope storage | 16,384 cells | Selected-entry route |
| Depth of a natural expression | 128 | Both routes |
| Type tree | 4,096 cells, depth 64, 64 immediate fields | Both routes |
| Symbolic affine coefficients and constants | Signed 128-bit integers, checked | Common judgment |
| Concrete natural arithmetic | Unsigned 32-bit naturals, checked | Closed instances |
| Helper template arithmetic | Signed 128-bit intermediate values, then a nonnegative unsigned 32-bit result | Closed instances |
| Alternatives of the constraint procedure | 64 per elimination problem | Common judgment |
| Symbolic variables of the constraint procedure | 32 per elimination problem | Common judgment |
| Elimination pairs of the constraint procedure | 50,000 | Common judgment |
| Retained constraints of the constraint procedure | 4,096 | Common judgment |
| Aggregate function calls, with Nat helper calls | 1,024 | Selected-entry route |
| Call depth | 16 | Selected-entry route |
| Aggregate fold iterations | 1,024 | Selected-entry route |
| Emitted source-order steps | 10,000 | Selected-entry route |
| Charged storage | 100,000 cells | Selected-entry route |
| Work of finite lowering | 1,000,000 units | Project route |

Limits that apply to these capacities:

- The constraint procedure checks its limits before it generates an
  elimination pair. It rejects if the pair count would exceed its limit or
  the retained set is at its limit. All its storage also consumes the
  preparation budget.
- The constraint procedure is not a complete solver for integer arithmetic.
  When a problem exceeds one of its capacities, the procedure rejects. It
  does not convert an unresolved premise into a successful assumption.
- The selected-entry route charges each concrete natural visit to the
  100,000-cell allowance. It charges each allocation of a helper argument or
  term to the same allowance. Each evaluated helper call counts toward the
  1,024-call allowance, which it shares with the specialization of runtime
  functions.
- On the project route, finite lowering charges its original natural visits
  and its helper work to the project-wide 1,000,000-unit allowance. It does
  not import the counters of the selected-entry route.
- Cache reuse does not remove call accounting.
- A capacity failure introduces no modular arithmetic.
- The parser, the constraint procedure, lowering, native checking and
  simulation have separate capacities. Each can reject an otherwise
  meaningful instance.
- Exhausting a budget is neither acceptance nor proof that a program has no
  meaning.
- Five obligations are distinct: compiler capacities, termination, ownership
  safety, computed quantum resources and checked target budgets.

### Limits of the routes

The two routes apply different limits to repetition counts and to the
operation descriptions that they materialize. The table states them.

| Limit | Project route | Selected-entry route |
| --- | --- | --- |
| A repetition count, at every nesting level | `0..=4096`, also inside an outer zero count | At most 256 |
| The exponent `e` of a count `2^e` | The count `2^e` must fit `0..=4096` | At most 8 |
| The product of nested repetition counts | At most 4096 in a direct runtime transform | At most 256 |
| An operation description that the route materializes | Six bits and 1024 steps, within the shared work limit | The aggregate limits of [Capacities](#capacities) |

Limits of the project route:

- The route evaluates symbolic counts and `2^e` with the complete original
  natural bindings and checked unsigned 32-bit intermediates.
- The product guard is specific to direct runtime transforms. An opaque
  operation description keeps its own materialization step and work limits.
- A controlled application uses the checked construction of a controlled
  circuit, and native evidence. The operation limit of six bits and 1024
  steps applies, and so does the shared work limit.
- A constructed adjoint such as `adjoint(power(U, k))(q)` uses the closed
  operation-provider profile, the exact basis and Adjointable evidence. Four
  limits apply: the literal-count limit, the six-bit operation limit, the
  step limit and the shared work limit. An adjoint of a bare name,
  `adjoint(name)(q)`, uses the finite transform path of the direct power of
  a name.
- For the direct form `power(name, literal)(q)`, the finite adapter checks the
  original body and the serial copies through the native gates. An actual
  operation parameter has a 1024-step limit and shared work accounting.
- A use of a sized operation requires a supported output profile.

Limits of the selected-entry route:

- The route applies its own count, exponent and aggregate-work limits. It
  rejects a count or a product above 256, and it rejects an exponent above 8
  (`limit`).
- When the route validates a selected entry, it does not check a false
  Meaning request in a generic body that the entry does not select.

Limits of both routes:

- The executable adjoint profile is Unitary. General isometry adjoints are
  unsupported.
- Concrete emitters have separate restrictions on the interfaces that they
  support for `Bits<n>` sizes.
- The capability rules enlarge the support of no concrete projection. Finite
  lowering and selected lowering keep their separate capacities and their
  explicit unsupported results.

### Provisional spellings and absent constructs

This section lists the provisional spellings and the constructs that the
language does not have.

- The spellings `static let` and `static fn` are provisional in 0.3.0. Their
  static category, their exactness and their authority laws are fixed. The
  typed-builder surface of 0.4.0 may select other spellings without
  introducing a second execution semantics.
- No general public `static fn`, `const fn` or builder API is stable. Those
  spellings, static lambdas, and quotation and splicing are open choices for
  0.4.0. A helper spelling that 0.3.0 adds later is provisional unless a
  separate decision stabilizes it.
- The scalar fragment and the provisional helpers of this chapter are
  supported. The bounded-const criteria and the collection criteria that
  [History](#history) names are not implemented.
- The language has no general static builder evaluation, no finite static
  collections and no general phase-table facility.
- Small Z, S and T phase schedules and computed generic sizes have
  independent checks. Those checks do not complete a general static
  collection API, the whole of the phase-table work, a source-preservation
  theorem or a generic QFT implementation.
- A generic QFT implementation is outside the human-selected development
  goal.
- This chapter supplies no arbitrary code execution, I/O, randomness, raw IR
  injection, trusted evidence constructor or floating-point substitute for
  an exact obligation.
- The bounded static contract does not discharge quantitative Resource
  Safety.

### Code, tests, proof, preservation and specification review

Code:

- The Rust frontend implements the rules of this chapter and produces
  untrusted proposals. Each resulting artifact and each independent request
  passes its native gate, as the
  [production boundary](production-boundary.md) describes.

Tests:

- Bounded regressions on small systems check the rules. They are
  implementation checks. They are not a theorem of general specialization
  preservation.
- The sized-source regressions cover guarded subtraction and affine
  equality, nonlinear refusal, original obligation spans, static dead arms
  and empty folds. They also cover forwarded premises and access, mutual
  cycles, complete bindings, repeat limits, and aggregate call, fold and
  storage accounting.
- Static evaluation need not enumerate the computational basis of a
  register. A generic identity fold keeps one definition and no source
  instructions as its width changes. Its fold counter counts the requested
  iterations, independently of the basis dimension `2^n`. The interface
  keeps the width, including the logical owner at `n = 0`.
- The bounded conformance test
  `static_accounting_does_not_expand_the_basis_domain_of_an_identity_fold`
  checks widths 0–3 and iteration counts 0, 1 and 3. It then independently
  accepts and executes each proposed identity with an external reference.
  Its simulation oracle enumerates small amplitudes after elaboration. The
  oracle is not the static evaluator.
- That test establishes no general complexity bound and no quantitative
  resource certificate. Other representations may need explicit finite data.

| Subject | Regression tests |
| --- | --- |
| Sizes, guarded subtraction, static dead arms, recursion and capacities | `tests/sized_source.rs` |
| Static bindings and the identity-fold accounting | `tests/static_naturals.rs` |
| Nat helpers | `tests/static_helpers.rs` |
| `requires` clauses | `tests/unified_requires.rs` |
| Static folds | `tests/qfor.rs` |
| Operation descriptions, applications and retired spellings | `tests/operation_parameters.rs`, `tests/checked_operations.rs`, `tests/parser.rs` |

Proof:

- This chapter claims no theorem of general specialization preservation. The
  checks on small systems establish no general source-preservation theorem.
- The two admitted guarantees `QS-QLV1-OWNERSHIP-2026-01` and
  `QS-QLV1-SCOPE-2026-01` keep their original-root scope.
- `QS-2026-01`, `PR-2026-01`, `RS-2026-01` for quantitative Resource Safety,
  and `EXACT-2026-01` are binding and pending at their broader scopes.
- General preservation of source and resources and the quantitative RS
  theorem are separate obligations.

Preservation:

- Native validity of an output does not prove that specialization preserves
  the meaning of the original source.
- The bounded materialization of specializations supplies no
  source-preservation theorem and no general caller-frame or cleanup
  guarantee.

Specification review:

- Reference meanings require human specification review, independently of
  acceptance, as the [authority hierarchy](authority.md) states. This chapter
  records no review of its rules.

## History

- This chapter describes the static fragment as `0.3.0-beta` implements it.
  It records the rules that
  [#28](https://github.com/MGYamada/Qleisli/issues/28),
  [#47](https://github.com/MGYamada/Qleisli/issues/47),
  [#44](https://github.com/MGYamada/Qleisli/issues/44) and
  [#63](https://github.com/MGYamada/Qleisli/issues/63) tracked.
- [#40](https://github.com/MGYamada/Qleisli/issues/40) fixed the class of
  static computations as the 0.3.0 decision. It deferred the public builder
  syntax to the typed meta-layer of 0.4.0, which
  [#60](https://github.com/MGYamada/Qleisli/issues/60) and
  [#61](https://github.com/MGYamada/Qleisli/issues/61) track. General static
  builder evaluation belongs to those two Issues. The helper spelling is
  provisional under the #40 decision.
- The maintainer excludes the unimplemented bounded-const and collection
  criteria of #63 from all of v0.3.0, including beta. The exclusion
  supersedes the earlier alpha-only deferral. It is not implementation
  completion. #63, which also held finite static collections and other
  phase-table work, is closed as not planned.
- [#33](https://github.com/MGYamada/Qleisli/issues/33) replaced the marker
  `[static name: Kind]` by `const`. Historical source bytes are historical
  inputs.
- [#194](https://github.com/MGYamada/Qleisli/issues/194) tracked the explicit
  threading boundary that the static folds implement.
- `power(U, count)(q)` preserves the contract of the retired `repeat_static`
  form. For a language primitive, it keeps the profile of the retired
  named-function repetition.
