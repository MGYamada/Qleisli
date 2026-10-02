<a id="qleisli-有限コア言語仕様-v0"></a>
<a id="1-範囲と規範の扱い"></a>

# Qleisli finite core language specification v0

English normative finite-core v0 contract for v0.2.x. [Grammar](syntax-v0.md),
[types](type-system.md), [modules](standard-library.md), [static operations](static-operations.md)
and [finite evidence](finite-contracts.md) refine it. Adoption, implementation,
finite validation and proof are separate; general source/Rust adequacy and
meaning preservation remain open ([formal scope](formal-core.md)).

## 1. Scope and normative interpretation

Finite Unit/Bit/ordered products; nonrecursive calls, total finite injective
lifts, sealed gates, static transforms, clean auxiliary scopes, observation and
classical branching. M1 adds compile-time operation descriptors/meanings/access
under [its contract](next-minor-spec.md). [Sized source](sized-corpus-source.md)
is a separate experimental API/CLI profile, not an extension of this grammar.

Q<A> owns resources; it is not a copyable state/computation effect. Unrestricted
free-vector-space bind and a strict monad theorem are not APIs/guarantees.
Accepted typing and implementation capacity are distinct. v0 excludes sized
variables, arrays, integers, arbitrary angles, runtime operations/closures,
higher-order quantum functions, recursion/dynamic loops, borrowing, with0,
Release0, nondestructive measurement, external operations and host I/O.
Iso<A,B>/Unitary<A,B>/lift(f) are metanotation. Explicit imports are required.
[Milestones](release-milestones.md) fix the completed finite V01 scope and open v1 goals.

<a id="2-型と文脈"></a>

## 2. Types and contexts

Bit is a coherent basis label; CBit is classical, with no implicit conversion.
Ordinary signatures contain no bare Bit. Types compare exact constructors,
arity/nesting and fields: flat/nested products, Unit factors, and
Q<(A,B)> versus (Q<A>,Q<B>) differ. bits(Unit)=0, bits(Bit)=1, product widths add;
Q<Unit> still moves exactly once. Every value containing Q is linear; naming a
mixed tuple moves it whole. Destructure to copy only classical components.
Types assert no state, eigenpromise, independence or success.

Γ;Δ ⊢ e:T ⊣ Δ'!ε separates copyable Γ and linear Δ; returned owners are disjoint
from residual Δ'. The complete quantum output also includes returned values and
pending/caller frames. Pure means Unitary or Iso. Basis context Ξ is isolated
from runtime Γ/Δ. [Type contract](type-system.md) fixes formation/capacities.

```text
Basis types A,B   ::= Unit | Bit | (A1,...,Ak)
Ordinary types T  ::= Unit | CBit | Q<A> | (T1,...,Tk)
Classical types C ::= Unit | CBit | (C1,...,Ck)
k = 2..64 immediate fields, with explicit nesting
```

<a id="3-束縛合成宣言"></a>

## 3. Binding, composition, and declarations

Names copy classical values or move entire linear values once; spent names remain
unavailable. Unit/tuple fields evaluate once left-to-right, retaining earlier
owners. let evaluates RHS before rebinding: let q=h(q) is valid; hiding a still
live owner is not. Patterns have distinct names; _ discards only classical
runtime values. Discarded expression statements must be classical. Blocks need
a final expression and return/explicitly consume all local quantum owners.

Runtime true/false:CBit and not/and/xor use ordinary truth tables, precedence
not>and>xor, left-associated binary operations, eager left-to-right operands;
false and measure_z(q) still measures q. Their own effect is Unitary; join
operand effects. Emit classical SSA Const/Not/And/Xor. Basis 0/1 remain distinct.

Calls require exact argument arity/types, evaluated left-to-right with pending
owners retained, and use the declared classification even if the body is weaker.
Functions explicitly declare signatures/effect; local let types are inferred.
Check every declaration, both arms, unused/zero targets; dependency graph is
acyclic including static function references. Declarations may be forward
referenced. Runtime live/spent locals hide ordinary/static/predicate callees
throughout lexical scope; basis calls use isolated Ξ.

<a id="4-効果と意味論"></a>

## 4. Effects and semantics

Unitary≤Iso≤Observe; tuples, sequencing and branches join effects; body≤declared
effect. Basis total functions are outside that ordering. Classical forms/moves,
gates, split/join, equal-width lifts, static/contract/clean-compute forms have own
effect Unitary; init0/growing lifts Iso; measure/reset/discard Observe. Declared
iso identity cannot be called from unitary. Classical forgetting is permitted:
quantum reversibility is checked per fixed classical input γ.

Pure output c(γ) depends only on γ, with Vγ:H_in→H_out; Iso requires V†V=I,
Unitary also VV†=I. Observe is one CP map Eγ,c per result, with a TP sum and
probability tr(Eγ,c(ρ)); hide results by summing maps, never branch amplitudes.
Local actions tensor identity on every remaining/reference system. Separate
owners may be entangled. Retain global phase, especially under control.

<a id="5-基底計算と単射リフト"></a>

## 5. Basis computation and injective lifting

Basis expressions: Unit, 0/1, variables/products, total Boolean operations and
nonrecursive basis calls; no ordinary calls, runtime capture or observation.
Basis information may copy/drop. Parameter patterns must match exact trees,
have distinct names across parameters, and do not remove ignored domain fields.
One tuple parameter remains one call argument. Packed semantic domain is Unit
for zero parameters, A for one, left-associated product for multiple parameters;
first field has low bits.

do p<-q;pure e evaluates/consumes Q<A> once; bind p against A in isolated Ξ and
require total e:B injective over the entire A domain. Names bind subtrees;
_ ignores labels, not owners; tuple patterns retain immediate arity. Return Q<B>
with V=Σx|f(x)><x|, coefficient +1; equal width Unitary, greater width Iso.
Equal-width explicit lifts may change type trees. Emit LiftBasis; independently
recheck its complete table/injection. A predicate used for compute need not be
injective.

Accept x→(x,x) (coherent basis copy, not unknown-state cloning), x→not x,
Unit→0, and (a,b)→(a,a xor b). Reject Bit→0, duplicate names/owners, pattern shape
mismatch, captured outer values, and two-bit XOR/AND alone. Removing an ignored
Unit factor is injective; removing an ignored Bit is not. do _<-q;pure () is
valid only for a singleton domain, still returning Q<Unit>. Calls never
implicitly unpack a product. Runtime f does not hide top-level basis f inside
Ξ; a do binder f does hide it. Predicate packing is specific to computed forms.

<a id="basis-product-boundary"></a>
<a id="6-封印された組み込み操作"></a>

## 6. Sealed built-in operations

All require explicit imports; consume distinct input owners/disjoint wires once
and return fresh ownership tokens. Gate wires persist; init/reset create fresh
logical IDs. Split/join preserve correlations and ordered axes; regrouping can
induce an output-coordinate permutation without a physical gate. [Module API](standard-library.md)
includes the compatible s/sdg/tdg/id/phase_eighth aliases.

H=[[1,1],[1,-1]]/sqrt(2), X=[[0,1],[1,0]], Z=diag(1,-1),
T=diag(1,exp(iπ/4)). CNOT |c,t>→|c,t xor c>; Toffoli
|a,b,t>→|a,b,t xor ab>. init0 prepares fresh zero, Iso. split consumes Q<(A,B)>
returns (Q<A>,Q<B>); join consumes two arguments in that order.

measure_z:Q<Bit>→CBit consumes the owner; Kb=<b|q tensor I_R,
Eb(ρ)=KbρKb†. discard:Q<A>→Unit sums basis Kraus maps (partial trace), including
Q<Unit>, Observe. reset:Q<Bit>→Q<Bit> sums JbρJb†,
Jb=|0>q'<b|q tensor I_R, Observe. Correlations are interpreted globally.
Reject old-owner reuse/aliased operands. Feedback may operate on another owner
or a freshly initialized wire; backend hardware reuse never revives a measured ID.

<a id="7-古典分岐の合流"></a>

## 7. Merging classical branches

if evaluates CBit condition first; true selects then, false else. Both arms
receive the post-condition linear context exclusively and are statically checked.
Require same complete result type, same outer consumed set, and no unreturned
local quantum owner. Match quantum result leaves by position/type and surviving
frames by original slots, including pending/caller holders. Matches cover every
live owner exactly once; issue fresh merged tokens/logical IDs. Classical result
phi matches positions and reads pre-merge values, never another phi output.
Join condition and both arm effects; branch-local bindings expire.

Returning (a,b)/(b,a) of matching types is valid; fresh preparations may merge.
Discarding q in only one arm or hiding a transformed q without returning it
rejects. IR ClassicalBranch phi renames ordered axes of the chosen arm, not
physical allocation, SWAP or loss of correlations.

<a id="8-静的な逆反復量子制御"></a>

## 8. Static inverse, repetition, and quantum control

adjoint(u,q), repeat_static(n,u,q), qif(c,q){0=>u0,1=>u1} are language forms.
Targets are statically eligible unary declared unitary Q<A>→Q<A>, without
classical ports; sealed/static-parameter eligibility follows [static contracts](static-operations.md).
Own effect Unitary joined with input effects; qif evaluates control before target,
requires disjoint owners and returns both, preserving control labels/phases.

Meanings U†, U^n, |0><0| tensor U0+|1><1| tensor U1. Even n=0 checks names,
types/body/evidence and passes ownership by identity. Closed deterministic
classical work may select a statically extracted branch, but both arms remain
checked and complete phi/output order retained. Q<Unit> scalar phases survive.
ApplyUnitary inversion reverses steps/permutations/phases, repetition expands
boundedly, control retains exact branches. Verify all axes/control disjointness,
full bijective tables/phases and output transport. Reject missing zero targets,
iso/preparation adjoints, classical-argument targets and control/target aliasing.

<a id="9-限定された補助計算"></a>

## 9. Restricted auxiliary computation

with_computed(q,f){|a|body} evaluates/consumes Q<A>, then resolves total packed
f:A→Bit. Private a owns a fresh auxiliary; source/other outer quantum owners are
masked in a complete frame. Outer classical values remain available; masked names
still hide callables. Binder may reuse a masked spelling without consuming that
outer owner. Body is Unitary, returns the same auxiliary slot and no extra owner.

After ordinary call expansion, its entire emitted sequence is auxiliary Z/T
or empty only. Accept a, z(a), t(z(a)); reject H/H;H, measurement, branches,
classical-SSA literals/Booleans and diagonal ApplyUnitary from adjoint/repetition.
Copying an existing classical value emits no instruction and is permitted.
No extensional matrix-equivalence exception applies.

Cf|x,b>=|x,b xor f(x)>; k=(4#Z+#T) mod 8 yields
Cf†WCf|x,0>=exp(iπk f(x)/4)|x,0>. This exact all-input/reference factorization
returns Q<A>, own effect Unitary, with zero/separated scratch. A lifetime or
sampled numerical zero is insufficient. Atomic ComputeUseUncompute validates
prepare/compute/use/inverse/release; no standalone Release0. Handwritten raw IR
has a broader protected-work form with its own checking rule, not source borrowing.

### Finite semantic-contract extension (2026-09-27)

Three-argument with_computed(q,f,u){|d,a|body} is separately specified by
[SC-SOURCE/SC-COMPUTED](finite-contracts.md). It isolates exact private data/aux
owners, captures no outer values, returns both in data/aux order and checks
actual W Ef=Ef u for independently fixed eligible logical unitary u. Raw
CertifiedCompute retains f/W/u for independent rechecking. Execution runs the
physical clean scope; static substitution uses its proved logical action.
Six-bit dense capacity allows five data bits plus aux, 1,024 steps/circuit and
shared exact work. This does not relax the older structural certificate.

### Function contract application (2026-09-27)

apply_contract(implementation,specification,input) evaluates input once before
resolving two ordinary unary unitary Q<A>→Q<A> functions; sealed gates require
ordinary wrappers. [FC rules](finite-contracts.md) check both actual bodies,
U=u with exact phase/output order, common tree and full source/dependency binding.
Retain immutable FunctionEvidence and CircuitAction::Contract under transforms;
normal ownership/control checking stays mandatory. Six public bits plus FC
limits. Equality to a chosen specification does not prove intended algorithm meaning.

<a id="10-コンパイルと実行の境界"></a>

## 10. Compilation and execution boundaries

Resolve/check every declaration; lower calls/forms to untrusted IR; independently
verify every producer's IR before execution. Contract actions retain evidence.
Closed execution requires parameterless observe main in root main.qli returning
only classical Unit/CBit/products, with no quantum owners left. Libraries need
no main.

Quantum instructions consume tokens/issue globally fresh outputs. LiftBasis
output starts with original ordered wires plus fresh wires when growing;
original-wire values may change. Branch merges freshly rename every result/frame
wire, including unchanged frames, with explicit selected-arm correspondence;
these are not allocation/SWAP. Live registers have ≤12 distinct ordered wires,
checked before u8 conversion/dimension shift. Token/wire freshness is global.

Located diagnostics report unsupported rules/limits; exact wording/order is not
normative. [Frontend](frontend-v0.md) and [machine results](machine-interface-spec.md)
fix codes/capacities. Never truncate counts/drop owners to fit. Reference floating
execution is separate from exact evidence/hardware capability checks. Independent
IR validity alone does not prove source preservation.

<a id="11-変更方針と次の工程"></a>

## 11. Change policy and next work

Update grammar/types/effects/ownership/semantics/IR correspondence together for
language changes and record compatibility. Ordinary definitions do not create
sealed primitives. [Versioning](versioning.md) and [milestones](release-milestones.md)
govern releases. Current mathematical derivations/component proofs do not prove
all Rust acceptance/lowering paths. General source and backend preservation,
production Soundness/Physical Realizability/Resource Safety and general v1
algorithms remain open. Draft notation grants no API.
