# Type, effect, name, and scope judgments for finite core v0

Status: **syntax-complete rule presentation and local paper lemmas**
(2026-09-26). This English supplement makes the typing and name premises of
the [v0 specification](language-spec.md) and [resource calculus](source-resource-rules.md)
explicit. It adds no accepted syntax, coercion, primitive, or library API.
The rules below and the resource transitions together cover every current
source AST constructor. This coverage is not a proof that the Rust frontend
implements the rules, nor a completed source soundness theorem.

The local results T1–T3 concern basis evaluation, deterministic judgments,
scope projection, and conservative effects. They are paper proofs, not Lean
proofs. [S1–S4](source-semantics.md) and [F1–F5](static-semantics.md) supply
conditional semantic correspondence; their implementation premises remain
open. Capacity and diagnostic ordering are separated from successful rules.

## 1. Types and judgment interfaces

Type formation is inductive, with **exact tree equality**:

```text
---------------- B-UNIT      --------------- B-BIT
Unit basis                  Bit basis

A basis    B basis          A basis
---------------- B-PAIR     ---------------- T-Q
(A,B) basis                 Q<A> ordinary

---------------- T-UNIT     ---------------- T-CBIT
Unit ordinary               CBit ordinary

T ordinary    U ordinary
------------------------- T-PAIR
(T,U) ordinary
```

These are all formation rules. In particular `Bit` is not an ordinary type,
and `CBit` and `Q<A>` are not basis types. There is no implicit flattening,
reassociation, unit removal, or conversion from `Bit` to `CBit`. Ordinary
functions can have different input/output type trees; a static target has
the stricter identical single-register interface.

Define `classical(Unit)=classical(CBit)=true`,
`classical((T,U))=classical(T) and classical(U)`, and
`classical(Q<A>)=false`. Set `linear(T)=not classical(T)` for ordinary types.
Thus a whole mixed pair moves, and `Q<Unit>` remains linear. Use
`bits(Unit)=0`, `bits(Bit)=1`, `bits((A,B))=bits(A)+bits(B)`.

Let `D` record declaration identities `(module,name)`, kind, parameter list,
result type, body, imports, and visibility. Let `E,F,R,H` be the visible
bindings, opaque pending frame, slot store, and issued-ID history of the
resource calculus. A live binding has an exact type and lexical identity;
a spent marker retains its name and identity. Write

```text
D ; m ; Xi |- b : A                         basis typing
D ; m ; Xi ; eta |- b evaluates to a : A     basis evaluation
D ; m ; E ; F ; R ; H |- e => v:T ! eps ; E' ; R' ; H' |> P
```

`eta` assigns a well-typed basis label to every variable of `Xi`. The last
judgment elaborates an ordinary expression in module `m`, returns a symbolic
value, derives its effect, and emits IR `P`. Its input invariant is
`WF(E,F,R)` and its output invariant is `WF(E',F++[v],R')` from R1. Classical
SSA visibility and fresh IDs are checked as part of those rules. No judgment
has permission to drop a quantum holder merely to make its conclusion true.

Use `U`, `I`, and `O` for `Unitary`, `Iso`, and `Observe` in rule displays,
with `U <= I <= O` and `eps join eps' = max(eps,eps')`. The empty join is `U`.
In displays below, `D,m` and the sequentially threaded histories and IR are
omitted when unchanged. Statement IR is concatenated in evaluation order;
`if` emits a structured branch. Fresh-name choices are immaterial up to
consistent renaming, not up to quantum phase.

## 2. Names, declarations, and project acceptance

`Resolve(D,m,f)` first selects a declaration named `f` in module `m`, then an
explicit import of `f`. If neither exists it fails. The project loader rejects
duplicate declarations and import/local collisions, so there is no accepted
ambiguous choice. Every imported source declaration, including a basis
declaration, must be public in its defining module. Importing an imported
name does not reexport it. Sealed
operations are available only through their known explicit imports.

The expression context additionally checks local hiding:

| Occurrence | Required local lookup and timing |
| --- | --- |
| Ordinary value `x` | Read only `E(x)`; require a live value. A declaration is not a first-class value. |
| Ordinary call `f(es)` | Require `f` absent from `dom(E)` and resolve it before elaborating the arguments. |
| Basis value `x` | Read only `Xi(x)`; runtime environments are inaccessible. |
| Basis call `f(bs)` | Require `f` absent from `dom(Xi)` and resolve a basis declaration. |
| `adjoint` / `repeat_static` target | Check hiding and resolution in the residual environment after the quantum input expression. |
| `qif` targets | Check both names after control and target evaluation, in their common residual environment. |
| `with_computed` predicate | Check hiding and resolution after source expression evaluation. |

Spent local names are in `dom(E)`. They hide functions until their lexical
scope ends. A callee body resolves its names in its **defining module** and
fresh parameter environment; it does not inherit caller bindings. Static and
basis operands name declarations rather than operation-valued expressions.

For each declaration require distinct parameter names and well-formed
parameter/result types for its kind. Basis declarations use basis types and
basis expressions; other declarations use ordinary types and blocks. Form
the function-reference graph from **all** syntactic call/reference sites,
including unused declarations, both branch arms, all basis calls, computed
predicates, both `qif` targets, and repetition-zero targets. Resolve each
reference and reject cycles. Module imports also have their own acyclicity
check. Forward declarations are allowed because dependency order, not text
order, determines checking.

The implementation's dependency prepass does not inspect local hiding; a
later expression check still rejects hidden callees. Consequently a program
with multiple violations may receive a dependency diagnostic first. Exact
diagnostic order is not a normative part of these rules.

For an ordinary declaration `eps_d fn f(x_j:T_j)->T {B}`, independently
introduce fresh well-typed symbolic parameter values. Put exactly their owned
slots in `R`, no extra frame, and bind the parameters in a fresh environment.

```text
E_params ; [] ; R_params |- B => v:T ! eps_b ; E_end ; R_end
no live linear binding in E_end          eps_b <= eps_d
--------------------------------------------------------- DECL
D checks eps_d fn f(x_j:T_j)->T {B}
```

The result type is the declared tree, and R1's boundary closure accounts for
every remaining slot through that result. Generate the corresponding raw
input/output ports and independently verify the IR, including the declared
effect bound. The verifier also checks equal total quantum input/output width
for `Unitary`. A function need not return its classical inputs or preserve
classical information: unitary classification is about the quantum operator
for each fixed classical input.

Check every declaration in the loaded project, including private, unused,
and bundled ordinary definitions. If declaration `main::main` exists, it must be an
`observe fn main()->C` with no parameters and classical `C`, even for library
checking. `compile_project` additionally requires its existence;
`check_project` permits a library with no root entry point. File layout,
reserved module names, filesystem checks, and numeric limits remain the
[project/profile](frontend-v0.md) obligations, not quantum inference rules.

## 3. Basis rules and T1: typed total evaluation

Basis types have finite nonempty carriers `L_A={0,...,2^bits(A)-1}`. Unit has
the singleton label 0. Pair encoding is
`pair(a,b)=a+2^bits(A)*b` for `a:A`, `b:B`.

```text
Xi(x)=A                  b in {0,1}
--------------- B-VAR    -------------- B-LIT    --------------- B-VALUE-UNIT
Xi |- x:A                Xi |- b:Bit             Xi |- ():Unit

Xi |- a:A    Xi |- b:B                    Xi |- b:Bit
------------------------ B-TUPLE         ---------------- B-NOT
Xi |- (a,b):(A,B)                        Xi |- not b:Bit

Xi |- a:Bit    Xi |- b:Bit       op in {and,xor}
------------------------------------------------ B-BOOL
Xi |- a op b:Bit

f absent from dom(Xi)    Resolve(D,m,f)=basis f(A_1,...,A_r)->B
Xi |- b_j:A_j for each j                    exactly r arguments
-------------------------------------------------------------- B-CALL
Xi |- f(b_1,...,b_r):B
```

Evaluation gives literals/unit their labels, reads variables from `eta`,
uses the displayed pair encoding and the usual Boolean truth tables, and
evaluates calls with the supplied labels bound to the callee's distinct
parameters. The callee uses its own module and has no captured `Xi` entries.
Check a basis declaration's body against its declared result under its exact
parameter types. There is no basis observation, ordinary call, recursion,
or runtime classical capture.

**T1.** With well-formed, checked, acyclic basis declarations, a derivation
`D;m;Xi |- b:A` evaluates uniquely to a member of `L_A` for every well-typed
valuation `eta`. Its result type does not depend on the input labels.

**Proof.** Induct on dependency rank and then the expression tree. Variable,
unit, and literal rules have unique well-typed values. Pair encoding maps the
two inductively bounded labels into exactly the product carrier. Boolean
truth tables are total on bits and return bits. In a call, the hypotheses
give all argument labels; exact types make a well-typed parameter valuation,
and the lower-rank callee induction gives its unique declared result. This
also proves termination because both expression descent and call rank are
well-founded. Every carrier is nonempty, so a full table check cannot pass
vacuously by having no input rows. No injectivity conclusion follows.

For an expression outside a basis declaration, use a synthetic dependency
rank above all its called declarations. Descending into argument subexpressions
decreases tree size at that rank; entering a callee body decreases rank.
Basis types are also unique: each expression constructor has one rule form,
variable and declaration lookups are functional, and operand-type checks use
exact equality. Structural induction therefore rules out two different result
types for the same context and expression.

For table generation, package parameter types as
`Pack([])=Unit`, `Pack([A])=A`, and
`Pack([A1,...,Ar])=(...(A1,A2),...,Ar)` for `r>=2`. Enumerate the domain in
the stated label order. This packages a table's domain; it does not replace
the syntactic arity/type checks of a basis call by a unary product argument.
The Rust implementation checks every table row; T1 is a mathematical lemma,
not a proof of that implementation or its capacity checks.

## 4. Values, argument lists, patterns, and blocks

`UNIT` returns `():Unit` with effect `U`. `COPY` reads a live classical value
without changing `E`; `MOVE` reads a live linear value and spends its whole
binding. Both have effect `U`. They fail on missing or spent value names.

```text
E0 ; F       ; R0 |- e1 => v1:T1 ! eps1 ; E1 ; R1
E1 ; F++[v1] ; R1 |- e2 => v2:T2 ! eps2 ; E2 ; R2
------------------------------------------------------ PAIR
E0 ; F ; R0 |- (e1,e2) => (v1,v2):(T1,T2)
                         ! eps1 join eps2 ; E2 ; R2
```

Define `ARGS` by the same left-to-right threading: the empty list returns
no values, effect `U`, and unchanged contexts; a nonempty list elaborates its
head, holds that entire result in `F`, and elaborates the tail. Earlier
classical and quantum actuals are not reevaluated or captured by later names.

`Bind(E,p,v)` additionally carries the set of names seen in this **one whole
pattern**, initially empty. Its complete rules are:

- `P-NAME`: install `v:T` at a fresh lexical binding identity. The name must
  not already have occurred in this pattern or hide a live linear binding.
  Replacing a classical binding or spent marker is permitted.
- `P-WILD`: accept `_` exactly when `classical(T)`. No binding is installed.
- `P-PAIR`: require `v=(v1,v2)` and bind both subpatterns left to right,
  sharing the pattern-name set. The product tree is not flattened.

A block has a list of statements and a mandatory final expression. Its
statement-sequence rules are:

```text
E ; F ; R |- e => v:T ! eps ; E1 ; R1
Bind(E1,p,v)=E2
E2 ; F ; R1 |- rest => w:T_out ! eta ; E3 ; R3
--------------------------------------------------------- LET
E ; F ; R |- let p=e; rest => w:T_out ! eps join eta ; E3 ; R3

E ; F ; R |- e => v:T ! eps ; E1 ; R1    classical(T)
E1 ; F ; R1 |- rest => w:T_out ! eta ; E2 ; R2
--------------------------------------------------------- SEQ
E ; F ; R |- e; rest => w:T_out ! eps join eta ; E2 ; R2
```

At the empty statement list, elaborate the final expression and keep its
value/effect. `LET` transfers the pending RHS value into bindings; `SEQ`
forgets only a classical result. Neither adds an effect or physical operation.

`BLOCK` saves its entry environment `E0`, elaborates this sequence in a local
environment `L`, then applies `Close(E0,L)`:

1. Reject any live linear binding introduced within the block that remains
   in `L`, even if its spelling, type, and slot equal an entry binding's.
2. For each originally live linear binding, retain it only if that same
   lexical binding remains live. Otherwise return its spent marker.
3. Restore every entry classical binding and entry spent marker; remove
   names introduced in the block. Keep the final result as a separate holder.

Outer linear bindings may pass through a block unused; declaration exit
additionally requires all parameter ownership to be consumed or returned.
An inner block cannot restore a consumed outer quantum value. Its classical
rebindings do not assign to the outer classical variable. These projections
are why branch environments can be compared after their local names vanish.
Expression blocks occur as declaration, branch, and computed bodies; braces
do not introduce an additional standalone expression form in v0.

## 5. Calls, sealed operations, and coherent lift

For an ordinary user call, first apply the name rule in §2. Let its resolved
signature be `(T_1,...,T_r)->T ! eps_d`. Require exactly those argument types
from `ARGS`, then bind the **values** to fresh formal identities. Check the
body and its boundary in the defining module as in `DECL`, with all suspended
caller holders and earlier surrounding pending values in its opaque frame.
Its result has type `T`. The caller's residual environment is the one left
by its argument evaluation; only current store metadata of framed slots can
be renamed by a callee branch.

```text
f absent from dom(E0)    Resolve(D,m,f)=ordinary (T_j)->T ! eps_d
E0 ; F ; R0 |- ARGS(es) => vs:(T_j) ! eps_a ; E1 ; R1
callee body/boundary succeeds on vs, with caller holders framed
-------------------------------------------------------------- CALL
E0 ; F ; R0 |- f(es) => v:T ! eps_a join eps_d ; E1 ; R2
```

For a sealed name, use the same argument rule and the following exact schema
instead of a source body. `A,B` are metalevel basis types, not source generics.
Every quantum argument is a distinct owned slot with disjoint live wires.
Store transitions and fresh IDs are those of the resource calculus.

| Sealed name | Argument list | Result type | Own effect / IR |
| --- | --- | --- | --- |
| `init0` | empty | `Q<Bit>` | `I / Init0` |
| `h`, `x`, `z`, `t` | `Q<Bit>` | `Q<Bit>` | `U / Gate` |
| `cnot` | `Q<Bit>, Q<Bit>` | `(Q<Bit>,Q<Bit>)` | `U / Cnot` |
| `toffoli` | `Q<Bit>, Q<Bit>, Q<Bit>` | `((Q<Bit>,Q<Bit>),Q<Bit>)` | `U / Toffoli` |
| `split` | `Q<(A,B)>` | `(Q<A>,Q<B>)` | `U / Split` |
| `join` | `Q<A>, Q<B>` | `Q<(A,B)>` | `U / Join` |
| `measure_z` | `Q<Bit>` | `CBit` | `O / MeasureZ` |
| `reset` | `Q<Bit>` | `Q<Bit>` | `O / Reset` |
| `discard` | `Q<A>` | `Unit` | `O / Discard` |

Join the own effect with the argument effects. `discard` has effect `O` even
on `Q<Unit>`. `split` requires an actual product basis tree; equal width is
insufficient. CNOT has two arguments; one ordinary pair argument does not
satisfy its arity. These operations are the already sealed names in
`std::quantum` and `std::observe`, not new APIs.

For coherent lift, define `LiftEffect(A,B)=U` for equal bit counts and `I`
for increasing bit count. A total injection between these finite bases cannot
decrease bit count.

```text
E ; F ; R |- e => q(s,A):Q<A> ! eps ; E1 ; R1
D ; m ; {x:A} |- b:B       f(a)=eval(b,x=a) for every a in L_A
f is injective            transition LIFT(s,A,B,f) gives R2
------------------------------------------------------------- LIFT
E ; F ; R |- do x <- e; pure b => q(s,B):Q<B>
                                  ! eps join LiftEffect(A,B) ; E1 ; R2
```

`{x:A}` is the **whole** basis context. Outer runtime names are not added to
it. Top-level basis callees still resolve in module `m`. T1 supplies totality;
injectivity is a separate table check, independently rechecked by `LiftBasis`
verification. Equal-width lifts may change basis type trees without adding
an implicit coercion anywhere else in the language.

## 6. Classical and coherent control, repetition, and computed scope

For `if`, first derive a `CBit` condition. Check both arm blocks from that
residual environment and store; share the issued-ID history across their
checks. The branch rule is

```text
E0 ; F ; R0 |- ec => c:CBit ! eps_c ; E1 ; R1
E1 ; F ; R1 |- B_then => vt:T ! eps_t ; Et ; Rt
E1 ; F ; R1 |- B_else => ve:T ! eps_e ; Ee ; Re
Et=Ee     CompletePhi(vt,ve,Rt,Re,R1)=(v:T,R2)
------------------------------------------------------------ IF
E0 ; F ; R0 |- if ec {B_then} else {B_else} => v:T
                  ! eps_c join eps_t join eps_e ; Et ; R2
```

`CompletePhi` is exactly the five conditions and classical-SSA merge rule in
[resource rules §5](source-resource-rules.md#5-classical-branches-and-simultaneous-phi-interfaces):
equal result trees, identical consumption of outer lexical bindings, positional
quantum results, every residual frame slot, and complete single coverage.
It includes zero-width slots and earlier pending values. Classical phi inputs
are read from the frozen pre-merge scope. Static effects include both arms;
a known runtime condition does not remove the other checking premise.

For `adjoint`, `repeat_static`, and `qif`, use the complete
[StaticTarget and expression rules](static-operations.md#static-target-judgment).
They require declared `unitary` with exact `Q<A>->Q<A>` or sealed `h/x/z/t`
on `Bit`; check the whole target and independently verify/flatten it. The
conclusions are `Q<A>`, `Q<A>`, and `(Q<Bit>,Q<A>)`, respectively, with own
effect `U` joined with all input effects. Repeat zero retains every target
checking premise. `qif` holds the control in `F` while evaluating its target,
requires disjoint ownership, and checks both arms. F1–F5 specifies their exact
operator semantics; ownership alone does not justify inversion or control.

For `with_computed`, `Mask(E1)` keeps classical values and existing spent
markers, and replaces every whole live linear binding with an unavailable
marker retaining its name. The source and those hidden quantum values are
held in the private frame, alongside the original `F`. Install a fresh
auxiliary binding `a:Q<Bit>`; its spelling may hide a masked outer name, whose
actual ownership remains inaccessible in that frame.
`R_private` is `R1` plus the fresh auxiliary slot, token, and wire; hiding
outer bindings moves their holders into the frame, not out of that store.

```text
E ; F ; R |- e => q(s,A):Q<A> ! eps ; E1 ; R1
f absent from dom(E1)    Resolve(D,m,f)=basis (B_j)->Bit
Pack([B_j])=A           table f is total
Mask(E1)[a := fresh auxiliary q(sa,Bit)] ; F_private ; R_private
    |- B => q(sa,Bit):Q<Bit> ! U ; E_body ; R_body
no live linear binding in E_body
emitted B is a connected raw Z/T gate chain on that auxiliary, possibly empty
---------------------------------------------------------------------------- COMPUTED
E ; F ; R |- with_computed(e,f){|a| B} => q(s,A):Q<A> ! eps join U ; E1 ; R2
```

The result must be the **same auxiliary slot**, not merely a one-bit value
with the same type. Calls in the body use their declared effects. Thus an
`iso` identity call fails even if its emitted operation list is empty. A
classical branch, H/H pair, or static inverse/repetition fails the structural
Z/T certificate even when its mathematical operator happens to be diagonal.
This rule is intentionally intensional, not a matrix-equivalence decision.

Eliminate the private auxiliary only with the exact factorization proved in
R1's computed section and F3. Emit one `ComputeUseUncompute`, update the
source token, and retain its slot/basis and the residual environment `E1`.
The source expression's effect survives. No ordinary `Init0` effect is
exposed for this internal, certified auxiliary and no free-standing pure
release is added. The predicate need not be injective.

## 7. T2: determinacy and lexical projection

Fix well-formed acyclic declarations, complete sealed schemas, the above
typing rules, and the R1 transitions and complete-phi construction. Fresh
identifiers may vary; compare derivations after consistent fresh renaming.

**T2a.** A successful derivation from fixed input contexts has a unique result
type, derived syntactic effect, and residual visible binding status. This
does not assert uniqueness of the generated IR or symbolic SSA values:
CompletePhi permits reuse of a shared parent classical ID, and a fresh phi
with identical inputs can express the same result. The Rust implementation
chooses reuse, but no canonical IR policy is needed for this claim.

**Proof.** Induct on dependency rank and expression/statement structure.
T1 supplies unique basis types, labels and tables. Value rules select a
unique visible binding; `classical(T)` chooses copy versus move. Pair and
argument rules fix left-to-right residual contexts. Pattern structure fixes
its matching subvalues, distinct-name checks and newly introduced bindings.
`Close` depends on original binding identities, not a guessed comparison of
quantum state. Calls select a unique declaration and its fixed signature;
the lower-rank body induction fixes their successful result. Sealed schemas
and lift tables fix types and effects. Branch result types must agree, and
projected outer bindings and position-wise phis fix the interface types;
permitted choices of SSA names do not change them. Static and
computed rules have fixed interfaces, target checks, and certificate rules.
Every conclusion uses a uniquely specified effect join. These cases exhaust
the constructors in §9. This proves determinacy of this mathematical rule
system, not termination or determinacy of all Rust executions.

**T2b.** A successful block projection restores every outer classical binding
and cannot make a consumed original linear binding live again.

**Proof.** `MOVE` can change a live original binding only to spent. Rebinding
introduces a different lexical identity; it cannot retain the original one
by copying its spelling or slot. `Close` restores the original linear value
only when the same identity survives live, so every consumed or replaced
original remains spent. Classical bindings and entry tombstones are restored
by the other projection clause. Induction through nested blocks preserves
these properties. At a branch, both projected environments must agree; a
surviving local with the same name cannot conceal unequal outer consumption.
This argument explains the need for Rust's separate `rebound` set, but does
not prove that its snapshots implement all lexical-identity cases.

## 8. T3: conservative effects and IR erasure

**T3a.** Each derived effect is an upper bound on every component expression
effect used by its rule. At every ordinary call it includes the declaration's
effect, and declaration checking bounds the entire body by that declaration.
Thus using a semantically simpler body cannot silently lower the caller's
classification. This is the least effect specified by these syntax-directed
rules, not necessarily the least classification of its mathematical operator.

**Proof.** Value/pattern cases contribute `U`; sequencing, arguments, tuples,
and `if` explicitly take maxima. `CALL` joins the argument effect with the
declared effect, which bounds its checked body. Lift/sealed/static rules join
their own and input effects. The computed body must have effect `U`, while
its source effect is retained. Induction and the transitivity of `<=` prove
the claim. Declaration rejection uses this conservative bound even if a
later circuit transformation would erase an instruction or branch.

**T3b (conditional translation bound).** Suppose each emitted primitive and
structural IR rule has its stated verifier effect, and body expansion follows
these rules. Then the emitted IR's derived effect is at most the source
effect. Equality is not required.

**Proof.** Primitive cases use the schemas. Ordinary expansion can replace a
declared effect by its smaller body effect; the call rule still bounds it.
IR sequencing/branching joins the already bounded fragment effects. Static
circuits contribute `U`. Atomic computed IR contributes `U` under its checked
certificate, although its private proof uses an initialized auxiliary. Name
and pattern operations emit nothing. Induction gives the bound. This relies
on the stipulated IR effects and does not establish verifier correctness.

For example, `observe fn id(q:Q<Bit>)->Q<Bit>{q}` is a valid declaration.
Its raw body contains no observation, but a `unitary` caller of `id` is
rejected. A verifier looking only at expanded instructions cannot recover
that source declaration obligation. The source check and independent IR
verification therefore discharge different premises.

## 9. Constructor coverage and implementation audit

The table covers the variants in [ast.rs](../src/frontend/ast.rs), not proposed
future syntax. Parentheses that group an expression add no AST constructor.

| AST family / cases | Rule coverage | Current implementation |
| --- | --- | --- |
| `TypeKind`: Unit, Bit, CBit, Q, Tuple | §1, declaration role | `Compiler::ty`, `signature` in [compile/mod.rs](../src/frontend/compile/mod.rs) |
| `FnKind`: Basis, Unitary, Iso, Observe; `FnBody`: Basis, Quantum | §2–3, DECL | `compile_basis` in [basis.rs](../src/frontend/compile/basis.rs); `lower_function`, `call_user_inner` in [lower.rs](../src/frontend/compile/lower.rs) |
| `BasisExprKind`: Name, Bit, Unit, Tuple, Call, Not, Xor, And | B-VAR, B-LIT, B-VALUE-UNIT, B-TUPLE, B-CALL, B-NOT, B-BOOL | `eval_basis` |
| `PatternKind`: Name, Wildcard, Tuple | P-NAME, P-WILD, P-PAIR | `bind` |
| `StmtKind`: Let, Expr; `Block` final expression | LET, SEQ, BLOCK/Close | `block`, with `entry`, `local`, `rebound` |
| `ExprKind`: Name, Unit, Tuple | COPY/MOVE, UNIT, PAIR | `expr_inner` |
| `ExprKind::Call` | §2 name timing, ARGS, CALL / sealed schemas | `expr_inner`, `call_user_inner`, `sealed` |
| `ExprKind::If` | IF, CompletePhi | `branch`, `merge_results`, `merge_register` |
| `ExprKind::CoherentLift` | LIFT, isolated basis context, injectivity | `lift`, `eval_basis` |
| `ExprKind`: Adjoint, RepeatStatic, QuantumIf | StaticTarget, ADJOINT, REPEAT, QIF | `expr_inner`, `static_steps`, [circuit.rs](../src/frontend/compile/circuit.rs) |
| `ExprKind::WithComputed` | COMPUTED, private frame and structural certificate | `computed` |
| Modules, imports, declaration dependency graph, root entry | §2 and project/profile premises | [project.rs](../src/frontend/project.rs), `resolve`, `called_names`, `order`, `process_project`, `compile_project`, `check_project` |

The representation audit maps lexical identities to `Option<Value>` entries
and explicit rebound tracking; effects to `Lowerer::effect` snapshots and
joins; and pending frames to registers outside the active environment. These
are reviewed correspondences, not proved simulation relations.

Finite acceptance/rejection evidence is in
[tests/source_judgments.rs](../tests/source_judgments.rs), alongside existing
[compiler](../tests/compile.rs), [static](../tests/static_operations.rs),
[source-semantic](../tests/source_semantics.rs), and independent IR tests.
The new tests compare source acceptance with explicit expected types/effects
and scope rules, including cases where raw IR has a weaker effect. They do
not infer source soundness from acceptance or test the paper lemmas directly.

| New regression | Expected boundary |
| --- | --- |
| `declared_effects_survive_arguments_tuples_conditions_and_both_arms` | Six composition contexts retain an `Observe` declaration even with an empty expanded body; an accepted closed program has source declaration `Observe` but derived IR effect `Unitary`. |
| `branch_local_shadows_expire_but_moved_outer_names_remain_reserved` | A branch-local gate-name binding expires; an original moved binding still hides a gate or predicate, including zero-width ownership. |
| `basis_domains_and_branch_results_preserve_exact_product_trees` | A three-parameter predicate requires its left-associated domain including Unit; a mismatched branch result tree rejects, while an explicit injective regrouping lift accepts. |
| `basis_context_is_closed_and_has_its_own_callable_shadowing` | An ordinary name is absent from the isolated basis context, while the basis binder hides a same-named basis function; quantum capture rejects. |
| `computed_certificates_preserve_effects_and_outer_name_restrictions` | A unitary expanded Z chain is certified; stronger declared effects, a hidden outer gate name, and an erased source-allocation effect reject. |
| `ordinary_basis_and_computed_names_resolve_in_the_declaration_module` | Imported bodies use their own module's ordinary and basis helpers; the three independently predicted measured bits are all one. |

The last case uses the numerical reference executor with tolerance `1e-12`;
the remaining checks inspect acceptance, diagnostic categories for isolated
violations, and verified IR structure/effects. Diagnostic ordering among
multiple violations is deliberately not an oracle.

Local validation on 2026-09-26: all six new tests and all 130 Rust tests passed;
formatting and Clippy with warnings denied passed. The coverage table names
all 34 variants in seven AST enums, with `Block` separately accounted for.
Documentation checks validated 351 local targets, 29 tables in eight changed
documents, all six regression names, and the specification's 12 legacy anchors.
This validation does not machine-check T1–T3. Lean was not changed.

## 10. Remaining proof obligations

The presentation is complete by current **syntax cases**. Establishing its
adequacy for all v0 accepted programs and every Rust checking path remains
open, including snapshot/lexical projection, freshness/history, finite-table
enumeration, layout matching, resource-limit diagnostics, and verifier data
structures. T1–T3, R1, S1–S4, and F1–F5 have explicit mathematical premises;
covering every constructor does not discharge those implementation premises.

[Q1–Q3](source-soundness.md) now assembles the paper pure-operation and
instrument theorems for these derivations, using exact primitive meanings,
injection and cleanup evidence, and finite adaptive composition over arbitrary
references. Next establish each source-to-IR leaf correspondence and the
implementation's satisfaction of the derivation premises. Soundness of all
Rust-accepted programs, compiler correctness, algorithm success, and backend
or hardware correctness remain distinct tasks in the [roadmap](../ROADMAP.md).
