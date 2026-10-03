# Fixed-width operations and meanings (M1)

Implemented finite supplement; no general sizes, operation values, closures or new effect. [Frozen complete grammar and contract](https://github.com/MGYamada/Qleisli/blob/v0.2.7/docs/next-minor-spec.md) remains applicable. [Tests](../tests/operation_parameters.rs) are bounded evidence, not general source adequacy.

## Scope and limits

Static Op is a copyable phase-fixed unary Q<A>→Q<A> description, with separate meaning/access and no owner capture. Exact Unit/Bit/product trees include empty owners. Width 0..6; circuit 1024; repeat 0..4096; syntax/type depth64, type4096 nodes; 256 specializations/depth64; aggregate lowering1M/exact10M. Count controls/tensors, unused arguments and zero bodies. One immutable full-project snapshot retains comments/std/modules; charge before copying. Every receipt rechecks metadata/raw pairs/equations; public owned copies charge bytes. Limits do not guarantee 256 providers fit.

## Grammar and resolution

Explicit ordered static arguments, canonical Nat; shared static/runtime namespace, no captures/runtime operation values. Local/imported names only; meaning names an ordinary total unary basis function. Runtime arguments evaluate once left-to-right before statics in residual scope; live/spent locals shadow globals. Resolve header access first; check all declarations, acyclic providers and zero bodies. Existing adjoint/repeat/qif accept names/static parameters; bracket arguments may construct descriptions. Computed/apply_contract restrictions persist.

## Meanings and binding

permutation_by(f) requires bijective f; phase_by(phi) maps A→(Bit,(Bit,Bit)) with phase ζ8^(b0+2b1+4b2). Full trees, first-low labels and scalar retained. bind_op(u,m) freshly verifies closed declared unary unitary, complete source/dependency DAG, raw circuit and exact ordered equality. Plain transparent operations derive meaning from checked circuits; Op<A,m> additionally fixes an independent target. Names/digests/cache confer no evidence/access; scratch needs exact entry/exit and complete frames.

## Access judgments and composition

Body access must be explicitly declared: Controlled alone grants neither Apply nor Adjoint. Transparent checked circuits retain constructor-derived access; narrowing needs MINOR. Opaque unitarity grants none. Check cancelled/count-zero operands; extraction failure is unsupported. Generic iso/observe may call operations, but providers are declared unitary.

| Form | Meaning/access |
| --- | --- |
| inverse_op(U) | u†; swaps Apply/Adjoint, control through checked controlled inverse. |
| then_op(U,V) | vu, identical interface; both corresponding capabilities, inverse reversed. |
| tensor_op(U,V) | u⊗v, first factor low, disjoint owners; both capabilities. |
| controlled_op(U) | C(u), low control; Controlled(U), subsequent access from actual checked circuit. |
| repeat_op(n,U) | u^n; same access even n=0; bounded exact squaring. |
| conjugate_op(V,W) | vwv†; Apply/Adjoint(V) and requested W access. |

C(u) preserves even labels and applies u on odd labels; Unit scalar becomes diag(1,ζ8^k). Controlled conjugation uses V†/controlled-W/V with separate control and full-space V; encoded ranges need entry/exit proofs. adjoint requires Adjoint, repeat Apply, both qif arms Controlled. Preserve arbitrary references/phase.

## Lowering and acceptance

Abstract checking precedes specialization keyed by complete immutable binding. Resource-only placeholders grant no evidence. Rebuild concrete/zero/unselected cleanup; charge every expanded call/binding. Existing FunctionEvidence/Contract actions retain both programs, trees, source/dependencies and final independent attachment; no new core action. Execute implementation, not requested meaning.

N1 grammar/resolution/capture/cycles; N2 every-column/Unit/tree/control/scalar/collision/stale/layout; N3 capabilities/zero/conjugation; N4 frames/references/empty/effects; N5 receipt mutations/work/limits; N6 unchanged-client substitution/adapters/migration. Wrong meanings, missing access, iso/observe providers, shape changes and owner alias/reuse reject with located diagnostics. Unresolved generic obligations authorize nothing.
