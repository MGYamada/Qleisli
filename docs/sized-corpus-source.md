# Sized source: Rust pipeline and Python oracle

Separate bounded experiment/finite public AST unchanged. Rust generic preparation checks requires/guards; Python untrusted concrete oracle. Native/finite checking independently accepts proposals; source/native/execution/R14/H1-H5 open. [Limits/implementation](../src/frontend/sized.rs), [clients](../tests/fixtures/sized_clients/README.md), [sized corpus](../corpus/sized/README.md).

## Historical Python concrete source contract

Explicit modules/pub/imports/natural+Op params,Bit/Bits/exact tuples; nonnegative naturals/+/-; linear lets/calls/half-open same-type folds/static branches. Both/unused/empty bodies check names/moves/access/effects,zero owners retained/no captures/shadow/drop/coercion. Explicit H/X/CNOT/take/put/phase,resolve all imports; take[n,k],k<n preserves remainder order/put inverse. Full complex phase/axis/reversal tracing and actual H,never name-based replacement. Controlled phase exp(2*pi*i*j*a*b/2^k),k<=8/j<2^k. Transparent f/adjoint/control preserve exact argument groups/actual body; guarded self-import n-1,instance cycle/depth32 rejects. Full-content sharing incl premises/encodings/bytes retains execution cost.

Python caps64modules/64 KiB source/10,000tokens/delimiter64/AST128/calls-folds1024/10,000definitions/register8/live16/finite6. Static Op<Bits<e>> requires explicit Apply/Adjoint/Controlled/size premises incl zero; unitarity/Apply grant no control. Count<=256 or2^e,e<=8,nested product256/Bits<2^n> invalid. Abstract direct apply/adjoint unsupported; transparent bindings/modules actual/unused included. QPE forwards naturals/providers in callee order/full nested key/caller access; CLI flat bindings.

Iso/observe continuation: zero args/CBit/CBits/mixed tuples,classical copies/quantum moves,init fresh zero/measure consumes. Experimental empty/consume_empty Bits(0),empty_bits/prepend_bit CBits low-first,not std APIs. Only separately checked independent-init/disjoint-readout retiming; no feedback/outcome gates/reuse/allocated>16. Shared/zero/empty bodies retained. [Checkpoint](../tests/fixtures/authoring_sessions/measured-qpe-v021/checkpoint.md) real sources/diagnostics; no retiming theorem from numerics.

## Additive Rust source pipeline

Private syntax/spans/contextual keywords,one ordinary function/module,explicit natural/Op params,Bit/Bits/CBit/CBits/tuples,linear lets/static branches/folds/transparent calls. [Parser](../src/frontend/sized/parser.rs)/[generic checker](../src/frontend/sized/check.rs) validate both/empty arms,guarded subtraction/indices/access/effects/owners. Explicit module map/regular-file loader/u32 instantiation; external/provider pub even unused/qualified,never seal. Rational-relaxation solver accepts only proved contradiction,unsupported/exhausted rejects.

Preparation caps64modules/64 KiB each/1 MiB total/10,000tokens per module/syntax64/natural128/tuple64/type64+4096cells/scope16384. Solver checkedi128/32vars/64alternatives/4096constraints/50,000elimination pairs per query,not Resource Safety.

[Elaboration](../src/frontend/sized/elaborate.rs) retains source-order shared definitions/full trees/owners/classical IDs/steps/spans; only concrete folds expand. Init/readout/packing and unused/zero providers retained,unselected generic arms get no concrete premise. Register+CBits8/live16 incl caller,k8/repeat+nested256/specializations1024 incl hits/folds1024/calls16/steps10,000/valuecells100,000/traversal64/value4096/scope16384. Abstract Op unary/transparent multiarity exact group.

[Lowering](../src/frontend/sized/lower.rs) retains elaboration/precursor events in untrusted HierarchyProposal. Quantum-only unitary or chronological observe CBits/residual roots; classical-entry/iso unsupported. Actual-port H/X leaves,fresh equations/empty routing. After-observation gates/init reject; earlier init needs certificate. Definitions10,000/cache+descriptor16 MiB/each payload-request-precursor16 MiB/observe visits1024/depth16. Fourier factoring checks commutation/noncommuting order/full phase/owners.

[Initialization replay](../src/frontend/sized/lower/preservation.rs) retains original step/call/span/value/full frames incl empty/all crossed pure/init/readout/packing events; fresh source/header/effect/operation/frame checks reject omission/alias/mutation/extras. validate_initialization_moves requires fresh CheckedInstrument/byte-identical payload; trace10,000events/100,000framecells. FreshInitialization.commute proves reference fresh-zero law,not this Rust checker. Actual meaning K_m(G)A includes preparation.

### CLI entry point

qleisli sized check|run|sample|emit-proposal --entry=module::function --module=name=PATH (closure repeated),--nat=name=N,--operation=name=module::function,--operation-nat=name.parameter=N. check/run/sample require --kernel=PATH/instrument init validation. Exclusive independent --request or --qpe-provider; default self-comparison makes no named-QPE claim. verification scope/request_origin/source_meaning_verified/execution_authority explicit. run full coefficients,--basis=N(default0);observe sample shots1..1024/seed. Basis only run/sample; check usage2 before execution. emit-proposal --output untrusted/no kernel. Failures retain mode/source/request scope/no required-work estimate.

## Acceptance and limits

emit-proposal output installs atomically without overwriting existing files,
directories or symlinks, including dangling symlinks. Failed installation removes
the temporary sibling; emitted bytes remain untrusted.

Actual native inspection/exact Rust leaves/independent complex comparisons/spec review distinct. Preserve first attempts/diagnostics/counterexamples. Small QPE(1,3)/(2,4) and arithmetic0..3; retain historical(8,8) failure/no new maxima. Repeated increment is not efficient synthesis; numerics prove no named order/amplitude algorithm/general adequacy and [capacity](../tests/fixtures/qpe_capacity_v023/README.md) does not widen limits.
