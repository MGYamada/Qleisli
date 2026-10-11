# Ordinary #317 before-code contract — 2026-10-06 (Asia/Tokyo)

Status: reviewed ordinary implementation contract for the next bounded experiment and shared frontend integration. This is not a claim of current canonical API availability or completed validation. This is an ordinary language/library contract under existing QS-2026-01, PR-2026-01, RS-2026-01 and EXACT-2026-01, not a new constitutional interpretation or guarantee admission.

## Scope and exact QFT contract

The current #317 scope is 24 criteria: all original twenty plus the four later generic-QFT criteria. Retain their exact text and required status in the next caller-reviewed release requirements snapshot. The canonical semantic identity is `std::transform::qft<N>`. Define the positive Fourier family on `Q<Bits<N>>`, returning the same ordered basis, for static N >= 0:
`F_N[y,x] = exp(2*pi*i*x*y/2^N) / sqrt(2^N)`.
For N=0, F_0=[+1] is exact identity on the same Q<Bits<0>> logical owner, distinct from Q<Unit>. Existing native named Fourier requests reject zero; validate this case through the existing typed identity/composition path without changing that matcher. For positive N, axis zero has weight one; output-bit reversal is included in this exact operator. Every input owner returns, with no observation or auxiliary allocation; its principal effect is body-derived Unitary. The intended action remains F_N tensor identity on every external reference, with phase and axis order retained. Names or effect metadata do not prove this functional contract or grant inverse/control access.

Use ordinary checked generic .qli source, not a new primitive or compiler special-case for the qft name. The current executable static-parameter spelling is `qft[static N: Nat]` with calls `qft[N]` applied to `q`; `qft<N>` denotes the canonical generic semantic identity in this checkpoint. Do not advertise angle-bracket call syntax as implemented. Any final generic-call spelling change follows the common grammar work in #32 and its migration contract.

Retained `qft2` and `qft3` may remain optional specializations with their existing exact tuple interfaces. No implicit tuple/Bits coercion or width-based type identity is introduced. Their correspondence to the generic instances must state the explicit ordered basis encoding and check exact phase, entries and reversal. A future `qft4` may be a specialization; its mention does not require adding a new fixed API now. Preserve all original contracts, useful tiny circuits, source provenance and notices. Current target/coefficient/work limits remain explicit; unsupported exact instances reject rather than round or silently select weaker checking. A generic checked definition and bounded instance results do not establish a theorem for the whole family.

## Sequence after the frozen validation finishes

1. Preserve a local first-source experiment using ordinary inferred `fn`, the existing licensed Fourier body and an outer `if static N == 0` branch. Check only N=0,1,2,3, retaining real generic-checking or native-boundary failures; local success does not expose a canonical std API. Audit every public stdlib item and active caller. Record mathematical namespace/admission rules and the disposition of each fixed arithmetic/catch-all API; preserve current sources and counterexamples before migration.
2. Connect ordinary generic stdlib definitions to shared name resolution, generic checking, embedding and public project/selected execution paths before exposing the canonical family. Use one immutable source collection, AST/Resolution and complete common declaration checking; only then select finite/Raw/hierarchy lowering eligibility. Do not expose divergent per-profile std ASTs, omit incompatible unused/dead declarations, add a privileged QFT-name resolver, or treat the corpus function's name as a library contract. The current finite checker rejects Nat/static-fold bodies; sized loading reserves std and rejects existing basis/qif declarations. Registry injection alone cannot repair these generic frontend gaps.
3. Implement the family as ordinary source through the existing exact h/controlled-phase/register-structure operations. The retained Qualtran Fourier translation is useful prior evidence, with its license/provenance preserved; copying or changing frozen corpus material still follows corpus policy.
4. Perform one atomic active migration: singular std::transform, canonical qft family and subordinate specializations; retire ad-hoc arithmetic exports and std::routines, rehome mathematically justified APIs, and update imports, examples, corpus clients, documentation, fixtures and discovery metadata. Retain historical validation records unchanged.
5. Independently check small closed QFT instances and every retained fixed specialization against the exact contract and explicit interface encodings, including wrong phase/axis/reversal cases, fresh native acceptance and real public CLI/library paths. Add no new maximum-size generation. Source/effect tests, output-IR acceptance, general preservation proofs and quantitative resource certification remain distinct.
6. Append #152's consumer boundary: its 0.4.0 structural refactor consumes #317's frozen semantic identities/admission rules, generic QFT contract and specialization correspondences; it cannot resurrect retired catch-all or incidental demo identities. Keep #152's target and twelve criteria. Close #317 only when evidence covers all 24 criteria.

No protected Constitution text, human adoption/admission record, ledger status, dependency version, native acceptance rule, new certificate schema or project axiom changes are authorized by this checkpoint.

## Audited disposition and namespace admission

The current target inventory is ten public ordinary runtime functions and private `nonzero2`; none is a sealed primitive. Preserve the exact body/phase/instrument contract and notices while changing active paths.

| Current path | Exact contract | Disposition |
| --- | --- | --- |
| std::arithmetic::increment2 | y -> (y+1) mod 4, coefficient +1 | Local examples/tests; retire canonical std export |
| std::arithmetic::add2 | (x,y) -> (x,x+y mod 4), coefficient +1 | Local examples/tests; retire canonical std export |
| std::arithmetic::mul2_mod15 | y -> 2y mod 15 for y<15; fixes15, coefficient +1 | Local order-finding examples/tests; retire canonical std export |
| std::transforms::qft2 / qft3 | Positive F4 / F8, included reversal | Optional std::transform specializations of the one generic family |
| std::routines::hadamard2 | Ordered H tensor H | std::transform::hadamard2 |
| std::routines::reflect_uniform2 | 2P_++-I, exact fixed sign and cleanup | std::reflection::reflect_uniform2; keep nonzero2 private |
| std::routines::measure_x | Complete destructive X instrument, K_b=bra(b) H | std::measurement::measure_x |
| std::routines::measure_z2 | Complete ordered destructive two-bit Z instrument | std::measurement::measure_z2 |
| std::routines::parity_zz | Nondestructive parity, K_s=(I+(-1)^s Z tensor Z)/2, both data owners retained | std::measurement::parity_zz |

The Qualtran reflection2 corpus contract is I-2|++><++|, the negative of reflect_uniform2. Do not merge them or erase the relative phase. Namespace placement grants no authority. Public names denote mathematical operations; explicit algorithm choice belongs to a parameter/policy/configuration layer. Mathematical families own the canonical generic name; fixed sizes are subordinate specializations. Prefer singular semantic concept nouns.

`arithmetic` admits reusable parameterized arithmetic/number-theoretic operations independent of a fixed demonstration; `modexp<N>` is an intended shape and `primefact<N>` the reserved v1 factorization identity, neither an available operation merely from this record. `transform` admits named exact basis transforms with full phase/coordinate equations. `reflection` admits phase-fixed 2P-I with explicit projector/reference contracts. `measurement` admits complete outcome-indexed instruments with consumed/retained owners and outcome encoding. Audit existing foundation namespaces' admission rules against their actual catalogs before finalizing the normative Reference; do not replace routines with another empty bucket.

QFT specialization correspondence uses explicit ordered-label encodings E2(a,b)=a+2b and E3((a,b),c)=a+2b+4c. Require E_N U_fixed E_N^-1=F_N with exact scalar phase. Packing/unpacking must be explicit ordinary source with the original tuple trees and consumed empty remainder, not implicit width coercion. Preserve the first fixed circuits, historical validation sources and pinned upstream material while creating migrated active derivatives.

This contract applies existing interpretations to ordinary implementation; it does not exercise Guardian authority. All24 criteria remain required and open until their implementation and independent evidence are complete.
