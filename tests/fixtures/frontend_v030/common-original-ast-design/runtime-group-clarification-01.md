# Direct transformed runtime groups: ordinary before-code clarification candidate

This is a proposed ordinary correction to the overly broad unary-provider and
provider-cycle sentences in `contract-01.md` (SHA-256
`60d3508a0bff407cc9acd8d66baa141fab9ce093d23ec8e57cfc13ee54b835e1`).
It is not a Guardian interpretation, adopted specification, proof or completed
implementation. No source, test, CLI, native, build or capture execution was
performed to prepare this candidate. The constitution, edition 2026, adopted
QS/PR/RS/EXACT interpretations and two registered limited guarantees are unchanged.

The existing selected checker at before-code commit
`4d86a0975c6cd97fe5bb1cc71115a2180ad561d6` distinguishes runtime owner groups:
`sized/check.rs::provider` forms the single input's actual type at arity one,
otherwise the exact ordered tuple of input types, and requires a nonempty
quantum group equal to the declared result. Its direct Adjoint/Controlled rules
use that complete runtime type. `types.rs::quantum_group` accepts Q leaves or
nonempty nested tuples of such leaves. `sized/elaborate.rs::provider_type` and
`operation_step` retain the same complete concrete group and actual owner checks.
These are inspected code contracts, not newly executed baseline results.

Actual latest attempt 07 terminated with focused-integration exit 101. Its
`ghz_and_arithmetic_corpus_prepare_and_lower_through_rust` failed at the existing
`all_ones[n-1]` controlled target `(rest,target)`; the small transparent-group
control also failed at `(a,b)`. Both reported `controlled target requires one
Q<A> owner`. The retained stderr is
`implementation-01/validation/latest-attempt-07/05-focused-integration-tests.stderr.txt`
(5,950 bytes, SHA-256
`a33bc5f30ed03a3744bfc79393c6d4fc5026eb6100c2fbfb53470bd7b49f757a`);
stdout is 25,870 bytes, SHA-256
`d620898167fda29cda6925bd95f761e752232fc12e6bd2ae96b7e70913fe46f5`;
terminal `results.json` is 13,394 bytes, SHA-256
`8476e7ae8184a774d5800eeb295e4c95e908c35099a2fada55e117f373f88249`.
Other actual failures remain in those logs; this clarification addresses only
the runtime-group regression and does not relabel the attempt as successful.

The proposed distinction is precise:

- Opaque `Op<A>` formals, ordinary providers supplied to such formals, Meaning
  refinements, certified logical operations and FunctionEquality retain the
  existing one-input `Q<A> -> Q<A>` contract. `Operation.basis` continues to mean
  the finite basis A, never an ordinary tuple of separate owners. Existing
  `tensor_op` remains a packed `Q<(A,B)>` operation; no implicit split/join,
  packing, flattening, same-width conversion or capability grant is introduced.
- A directly transformed ordinary Name or Specialize target, including its
  transparent Repeat wrapper, instead has an exact runtime target type T.
  Arity zero rejects. At arity one T is that input's complete type; at larger
  arity T is the exact ordered tuple of the complete input types. T must be a
  nonempty tree whose leaves are Q owners, and must equal the declared result
  under the actual checked substitution and caller premises. `Q<Unit>` and
  `Q<Bits<0>>` are valid leaves retaining their owners and scalar phase. Ordinary
  Unit, Bit, Bits, empty tuples and mixed classical/quantum trees reject.
- Direct Controlled evaluates its control then target exactly once; direct
  Adjoint evaluates its input exactly once. The target must match T without
  conversion. Their result is respectively `(Q<Bit>,T)` or T. Exact nested
  shape, every owner's single consumption, axes and body phase remain intact.
  Resolve/check the operation through the original AST and lexical identities
  after this input evaluation, retaining current common diagnostic order.
- Direct Name/Specialize/Repeat must still have body-derived principal Unitary
  effect and the required Adjoint/Controlled implementation path. Actual Op
  arguments retain the recorded conservative transparent-provider access mask;
  an annotation, provider name or effect alone does not grant a path. Repeat
  checks its original count and child even at zero; concrete count/expansion
  limits remain. Other opaque constructors retain their existing basis rules.
- Add a distinct located pending `RuntimeGroupProvider` obligation bound to the
  original provider DefId, declaration/interface association, complete runtime
  interface and principal Unitary fact. The actual substituted input group,
  result and target equality are checked at the call. Its binding validation
  neither supplies transformation evidence nor proves source preservation or
  provider correspondence. Do not weaken the unary Provider, MeaningEquality,
  FunctionEquality or certified-clean binding guards to accommodate groups.
- An actual direct runtime transformed self-call to the identical DefId may use
  the existing proved Nat decrease check: every Nat does not increase and at
  least one strictly decreases under the caller guards. This includes the
  existing `controlled(all_ones[n-1])` recursion. It is not a general static
  provider permission: other recursive static/provider references, mutual
  dependencies, Basis/Meaning cycles, failed decrease and zero-count attempts to
  hide invalid references still reject through the checked graph.

Implementation should expose a direct-runtime transform judgment carrying T,
separate from the opaque-basis operation judgment. Both consumers receive the
same original-source facts before eligibility. Selected concrete provider/type,
ownership, transformation and native gates remain real. Finite materialization
retains its existing supported interfaces and must report unsupported concrete
group lowering honestly rather than reinterpret T as a packed owner or fall
back to another accepting route. Static bindings and CLI `OperationBinding`
remain strict opaque providers; direct runtime grouping does not widen them.

The bounded controls are the existing small transparent-provider Controlled and
Adjoint positives; repeated-owner, wrong nested tuple and classical-mixed
negatives; one-owner Bits<0> positive and ordinary Unit negative. Preserve the
existing packed static-tensor full-operator tests unchanged. Prepare/lower
`all_ones` at n=0..3 with the existing corpus consumers, then run only the
already-authored small native independent reference-column test (whose
`all_ones` cases are n=0..2). Its expected columns are defined by the classical
all-ones-controlled permutation, independently of proposed circuit meanings;
passing is bounded evidence, not a generic family/preservation proof. No maximum
case, new primitive, native matcher waiver, standard-library exposure or Issue
completion follows from this correction.
