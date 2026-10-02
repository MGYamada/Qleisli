# Source frontend: implemented finite profile

[Language](language-spec.md) and [grammar](syntax-v0.md) are normative;
[src/frontend](../src/frontend/mod.rs) implements this finite source boundary.
The complete Rust frontend and numerical executor have no general adequacy proof.

## Entry points and project loading

`check_project` checks all declarations, including unused providers, without
requiring main. `compile_project` additionally requires parameterless observe
main in main.qli returning Unit/CBit/finite classical tuples, arity 2–64, with
no owners remaining, then independently verifies emitted IR. Bundled std uses
the same checks. Source roots, visibility/imports and edition selection follow
[modules](standard-library.md) and [editions](language-editions.md). OS paths
remain OS strings, including non-UTF-8 where supported; portable diagnostics
must not lossy-encode identity. doc only parses one file and issues no evidence.

```sh
cargo run --bin qleisli -- check examples/bell
cargo run --bin qleisli -- run examples/bell
cargo run --bin qleisli -- run examples/phase_oracle
cargo run --bin qleisli -- run examples/feedback
```

## Checks and lowering

Resolution uses explicit imports in the defining module; all import/call cycles
reject. Calls check ordered argument arity/types and declared effects, move owners
and expand with fresh IDs. Products never unpack implicitly into arguments.
Blocks evaluate RHS before binding, reject live-owner shadowing/implicit disposal,
and return or explicitly consume local owners. Basis functions enumerate a total
finite table; do/pure additionally checks full-domain injectivity and emits LiftBasis.

Primitive contracts follow [language v0](language-spec.md); split/join retain exact
source trees and wire order. Classical branches check both arms and merge every
result/caller/pending owner with fresh IDs across arms; phi inputs are validated
before outputs. Classical operators evaluate both operands once in order.

Source qif/adjoint/repeat lower to independently checked ApplyUnitary. Static bodies
must meet [the static contract](static-operations.md), including same interface,
closed branch restrictions and checking zero repetitions. Restricted two-argument
computed use permits expanded identity/Z/T only, with outer quantum captures masked.
Three-argument computed use checks the retained joint-body equation and cleanup.
apply_contract independently checks both actual raw functions and retains immutable
bound evidence. [SC/FC](finite-contracts.md) gives eligibility, extraction and budgets;
no form relies on a supplied seal or checker success flag.

## Diagnostics and limits

Legacy CompileError retains category/path/span/one-based Unicode line-column.
Categories include Arity, TypeMismatch, Effect, UnknownName, RecursiveCall,
Ownership, InvalidEntry, Unsupported, Limit, Project, InvalidIr. Failed injectivity
is Ownership; parse/load wraps Project; contract failures retain InvalidIr.
Calls locate argument/call, body failures locate body; IR provenance locates source
operations. Exact mismatch reports first column/row coefficients; effect failures
retain cause and declared/derived effects. One error is reported; message prose
and future multiple-error order are not normative. [JSON](machine-interface-spec.md#diagnostics)
defines portable fields and codes; LF/CRLF are supported, bare CR is located failure.

Width <=12, syntax/expansion/basis/type/value depth <=64, type/value nodes <=4096.
One shared lowering allowance <=1,000,000 charges retention/copies/tables/snapshots/
phis across declarations and call expansion. Exact work <=10,000,000 per compilation
covers unused static providers and complete receipts, prepaid conservatively.
Snapshots are retained once per allocation at first provider/contract use: <=128
modules, each identity name <=4096 bytes, aggregate records including names <=1 MiB.
Each receipt still rechecks metadata and copied raw/pair cost; explicit public views
may materialize bounded copies. Input overrides do not override these budgets.

macOS holds parent descriptors and uses component-relative openat/O_NOFOLLOW,
without O_NOFOLLOW_ANY or a raised OS minimum. Listed Linux architectures hold
descriptors through readable /proc/self/fd, without link-following fallback.
Other targets retain filesystem trust assumptions. [Source bytes](machine-interface-spec.md#source-input-capacities-and-migration)
and [simulation limits](ir-prototype.md#reference-execution) are separate.

## Evidence and remaining obligations

[Frontend tests](../tests/compile.rs), project/static/algorithm tests, corpus complex
and instrument oracles, exact checking and actual-definition Lean proofs cover distinct
finite scopes. Commands exit 0 success, 1 load/check/run failure, 2 usage; run prints
approximate probabilities in tuple order, Unit contributing no bits. See
[examples](../README.md#try-it), [corpus](../corpus/README.md) and [rule ledger](rule-inventory.md)
for executable evidence; agreement is not general frontend or hardware correctness.
