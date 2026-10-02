# Selected M1 machine interfaces

Normative X1-X6 finite profile; product/format versions independent. Rust authoritative, source adequacy unproved. QIRF is Qleisli JSON, not LLVM QIR. [Interop](interop-m1.1.md)/[hierarchy](hierarchical-ir-spec.md) separate.

## Diagnostics

check/run/sample/emit-ir/verify-ir accept one --format=json anywhere (doc Markdown-only). One UTF-8 object+LF/empty stderr; write failure may use stderr. Exact flag selects JSON usage errors; exits0 success/2 usage/1 failure. Leading-dash paths need ./; command first remaining UTF-8 argument or empty.

Envelope {format:"qleisli.result",version:1,command,outcome,diagnostics,result}; all fields required, error needs error diagnostic/null result. Diagnostic {code,severity,message,primary,related}; related {message,location}; severity error/warning/prose unstable. Nullable location {path,start,end,line,column}: original half-open UTF-8 bytes, one-based Unicode scalar coordinates, project-relative slash/std:// paths; EOF empty allowed/no lossy identity. Artifact failures related JSON pointers/null locations. Closed codes usage/project/parse/unknown_name/recursive_call/type_mismatch/arity/ownership/effect/invalid_entry/unsupported/limit/invalid_ir/contract/capability/format/simulation/random_source/numerical; additions versioned. Capacity limit/other runtime simulation; unknown manifest metadata warns, --qrate explicit root.

Success: check {verified:true}, run {distribution:[{bits,probability}]} lexicographic, emit-ir {path}, verify-ir {verified:true,request_checked}. Finite probabilities [0,1], clamp only within inclusive2^-40 endpoints/no renormalization/cutoff. Located APIs use retained provenance, not messages/rereading.

Unused-manifest warning messages contain no host path. For an ancestor Qargo.toml
outside a selected source root, its location uses one ../ per source-root level
(for example ../Qargo.toml); other out-of-root locations remain null.

## Portable finite IR and evidence

emit-ir PROJECT --output=NEW exclusively installs complete temp sibling atomically. verify-ir ARTIFACT [--against=REQUEST] loads no source/network/compiler/plugins; without request, request_checked=false.

QIRF1 exact envelope {format:"qleisli.finite-ir",version:1,profile:"finite-v0",sources,programs,evidence,root,root_interface}. Strict UTF-8/JSON, reject duplicate/missing/unknown fields/tags/noncanonical integers; IDs u32/distinct namespaces, exact strings. Fixed wire keys/types are specified in [record codec](../src/interchange/codec.rs), [operations](../src/interchange/codec/operations.rs), [scalars](../src/interchange/codec/scalars.rs), [evidence](../src/interchange/codec/evidence.rs), not derived Rust names. Vec arrays/booleans literal; BasisType preserves Unit/Bit/Pair/Tuple>=3 fields, widths<=12/ordered wires. [Raw semantics](language-spec.md)/[SC-FC](finite-contracts.md) independently govern effects/owners/gates/phases/cleanup.

Sources unique nonempty NUL-free labels<=4096bytes/128 records, never filesystem instructions. Identity retains ordered unique source indices. Validate entire program/evidence DAG incl cycles/unused sources/objects; reconstruct distinct receipts once topologically through ordinary checks, then all programs/root. No private seal/Arc/matrix transport authority.

root_interface null or exact {input,output} bound to sole unary unitary quantum ports/no classical ports; retain trees/order incl empty,depth64/nodes4096. Never infer from counts/evidence/request. Null internally valid but fails --against; malformed interface invalid_ir/budget limit.

Limits16 MiB/depth128/1M JSON values/65,536 combined objects/1M raw-step nodes/graph32/source text1 MiB; SC six-bit/1024steps/expanded1M/shared10M exact also apply. Bound before allocation/deep drop. Aggregate identity1 MiB counts both names/receipt, each source path/text once; ordered snapshots shared without work resets.

### Reconstructed finite unitary leaves

UnitaryBoundary binds full identical trees/both ordered owner-shape-wire ports incl empty. check_unitary freshly imports QIRF1/2, verifies declared+derived Unitary/no classical ports, compares full exact matrix/phase with independent meaning. Private receipt retains bytes/boundary/program/matrix, full byte equality incl whitespace. One caller budget<=10M/dim64; multiowner/rectangular production transfer open.

### Exact finite matrix descriptions

{format:"qleisli.finite-matrix",version:1,domain:"zeta8-dyadic-v1",rows,cols,entries}, dimensions1..64/row-major. Scalar [a,b,c,d]=a+b*sqrt2+i(c+d*sqrt2); dyadic {numerator:string,denominator_bits:integer}: canonical decimal i128/no plus/leading zeros/-0,exponent0..126,zero exponent0/nonzero odd when exponent>0. Noncanonical format/excess limit. Rectangular descriptions allowed, unitary requires requested square dimension. Charge4/entry/no refund/deterministic JSON+LF; combined serialized matrix+payload<=16 MiB, bind original bytes. Reader alone proves no equation.

### Independently supplied finite requests

{format:"qleisli.request",version:1,signature,meaning:{tag,table},source_snapshot}; permutation full u16 table or phase8 table0..7, snapshot null/exact ordered {path,text}. --against requires both retained trees/signature/unary Unitary/exact matrix+phase/snapshot. Null/substituted equal-width trees contract failure; overwide port trees invalid_ir. No recompilation/source adequacy.

QIRF2 finite-meaning-v1 adds evidence tags circuit(v1 fields)/meaning(signature,implementation,meaning,identity), declared meaning name as specification. Fresh table/equality checks. v1->v2 tags circuit/preserves root_interface; reverse rejects meaning receipts. No reinterpretation.

## Sampling and typed trials

sample_closed no external/quantum outputs, fallible uniform-u64 RandomSource premise/fresh trajectory. Sum p0 ascending basis, one high53-bit draw even deterministic observation, choose0 iff u<p0/collapse. Reset/discard hidden measurements in program/ascending-wire order; old owners removed/reset fresh0. Selected classical arm only. Finite positive norm; drift2^-40+16*EPSILON*actual steps since normalization, observation/collapse/completion2^-40/no unused allowance/zero selected norm. Defaults16axes/hard20/1,048,576cells/1M actual steps per sample; nested dispatch/hidden draws charged, CLI aggregate10M/no partial output.

sample PROJECT --shots=N --seed=S requires canonical N1..1M/S0..2^64-1. Sequential splitmix64-v1: state+=0x9e3779b97f4a7c15; z=(state xor state>>30)*0xbf58476d1ce4e5b9; z=(z xor z>>27)*0x94d049bb133111eb; word=z xor z>>31,u64 wrap. JSON {rng,seed:string,shots:[{bits,execution_steps}],execution_steps}; same backend/program/seed reproducible, cross-platform rounding not promised.

run_trials(max,callback): one-based attempts, Accepted stops/Retry ordered reasons/Execution aborts; max<=1M, invalid no callback/zero Exhausted0/fresh quantum attempt. Factoring2<=N<2^32,1<a<N,coprime,m1..32: convergents y/2^m,1<=r<N/a^r=1; increasing-prime reduction to minimal even period, validated nontrivial p*q=N. Distinguish invalid_candidate/odd_period/trivial_factor; checkedu128/1M iterations per trial. Even-N/gcd prechecks separate.

## Source input capacities and migration

Defaults1 MiB/file,16 MiB/distinct canonical files+bundle; count before UTF-8/stream<=limit+1/deterministic paths. I/O/UTF-8 project/excess-overflow limit/no fabricated span. Positive-u64 --source-bytes/--project-bytes versus exclusive --legacy-source-limits; old APIs Legacy, SourcePolicy APIs explicit. Snapshots1 MiB; overrides bytes only/reduced acceptance MINOR.

## Required conformance before shipping

X1 JSON/spans/flags/exits; X2 all nodes/DAGs/mutations/limits; X3 fresh independent typed request incl empty/tree mismatch; X4 seeded/Bell/reset/feedback/statistics; X5 retries/failures/periods; X6 bytes/UTF-8/bundle/legacy. [Tests](../tests/cli_json.rs)/[diagnostics](../tests/diagnostics.rs)/[interchange](../src/interchange/mod.rs)/[sampling](../src/sim/sampling.rs)/[factoring](../src/host/factoring.rs) retain executable detail, not fresh execution report.

## 0.2.0 host API mapping

Export/convert/import retain trees/order, export_with_meanings sealed v2 descriptions. CLI closed Observe QIRF2/null root is not unary request. Rust typed producers retain trees; no production Lean receipt/new source primitive.
