# Qleisli finite core language specification v0

English normative v0.2.x. [Syntax](syntax-v0.md),[types](type-system.md),[static](static-operations.md),[SC/FC](finite-contracts.md),[frontend](frontend-v0.md) jointly specify forms/APIs/lowering. Rust/source/backend adequacy unproved.

## 1. Scope and normative interpretation
Finite Unit/Bit/products,total nonrecursive calls,injective lifts/sealed gates/static transforms/explicit observation+cleanup. Q owns rights,not states/effects. No recursion/arbitrary angles/runtime closures/borrowing/implicit release/host I/O/free-vector bind. [M1](next-minor-spec.md)/[sized experiment](sized-corpus-source.md) separate.
## 2. Types and contexts
Classical Γ copies,linear Δ moves,basis Ξ isolated. Full result/residual/pending/caller interfaces,zero-width owners/ordered tree preserved under [type contract](type-system.md). Separate owners imply no separability/eigenstate/success.
## 3. Binding, composition, and declarations
Arguments/tuples once left-to-right,RHS before rebinding,whole mixed value moves/destructure classical fields to copy. Distinct binders; _/statements discard only classical. Every owner returned/explicitly consumed,no live hiding. CBit eager not>and>xor,left-associated: false and measure still observes. Exact arity/type/declared effect; every declaration/both arms/zero body/dependency cycle checked. Forward declarations; live/spent locals hide callees.
## 4. Effects and semantics
Unitary<=Iso<=Observe,join operand/arm effects/body<=declared. Pure classical results depend only on classical inputs. Iso V†V=I;Unitary also VV†=I. Observe CP/TNI outcomes/TP sum,hidden outcomes sum maps not amplitudes. All local operations tensor reference identity/full scalar phase; iso-declared identity not unitary target.
## 5. Basis computation and injective lifting
Total isolated Unit/0/1/products/Booleans/calls; exact distinct patterns. Domain Unit/one parameter/left-associated multiargument product,no ordinary-call unpacking. do p<-q;pure e consumes Q<A>,full-domain total injection A->B/coefficient+1/Q<B>; equal width Unitary/growth Iso. Ignored Bit cannot disappear; Unit may but Q<Unit> returned. x->(x,x) coherent basis-copy,not cloning; compute predicates may noninjective.
## 6. Sealed built-in operations
Explicit imports/disjoint wires/distinct owners/fresh outputs. H normalized Hadamard,X flip,Z diag(1,-1),T diag(1,zeta8); [phase aliases](frontend-v0.md#initial-standard-library-organization). CNOT/Toffoli XOR target under controls. split/join transfer low-first owners/correlations;init0 fresh-zero Iso. measure_z consumes Bit/Kraus <b|,discard partial trace incl Unit,reset consumes/prepares fresh0/Kraus |0><b|. Hardware reuse never revives owner.
## 7. Merging classical branches
Both arms from post-condition context,identical result trees/outer consumed sets/no local leaks. Match every result/frame/pending/caller owner once incl empty;fresh merged IDs/positional axes. Classical phi all premerge inputs before outputs. Selected execution/locals expire/effects join; result reorder may valid,one-arm disposal not.
## 8. Static inverse, repetition, and quantum control
[Static contract](static-operations.md): unary declared same-tree unitary/no classical ports/access,both+zero bodies checked,U†/U^n/diag(U0,U1),control-first/distinct retained owners/phase-exact ApplyUnitary. No iso inverse/aliasing.
## 9. Restricted auxiliary computation
Legacy with_computed(q,f){|a|body}: consume input then resolve total packed predicate/private fresh aux; outer quantum masked/classical available,masked names still hide callees/binder may reuse spelling. Same aux returned,expanded body empty/Z/T only (not H-H/branches/SSA/transformed diagonals). Cf XOR computes; k=(4#Z+#T)mod8 yields exp(i*pi*k*f/4),aux exactly0/separated for every reference,no Release0.

Certified three-argument form captures neither outer quantum nor classical,returns ordered data+aux,retains actual scope/checks WEf=Efu under [SC](finite-contracts.md). apply_contract evaluates input once before resolution/full signature+phase+source+dependency equality under FC; immutable evidence survives transforms,not intended-meaning proof.
## 10. Compilation and execution boundaries
Untrusted lowering/independent raw checks for every producer; entry/loading/limits in [frontend](frontend-v0.md). Fresh IDs/lift appended wires/full-frame positional phis not SWAP; width12 before narrowing. Floating execution not evidence.
## 11. Change policy and next work
Joint syntax/type/effect/owner/semantics/lowering changes follow [versioning](versioning.md). [Theorem/v1 gates](release-milestones.md) open; notation not API.
