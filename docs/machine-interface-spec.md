# Selected M1 machine interfaces

X1–X6 are implemented in the finite profile; [0.2.0 evidence](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/releases/v0.2.0.md)
records execution. Formats have independent versions: product bumps do not reinterpret
them. Existing check/run/Rust IR/exhaustive execution remain compatible.
[Interop](interop-m1.1.md) separately specifies Python/OpenQASM/QIR; QIRF below is
Qleisli JSON, not LLVM QIR. [Phase-word](lean-kernel-migration.md#first-executable-slice)
and hierarchy protocols are experimental, not production receipts. Rust remains
authoritative. Desugaring emits untrusted, meaning-preserving existing-core IR;
future domains/approximations need separate bound contracts, not extra implicit tags.


## Diagnostics

check/run/sample/emit-ir/verify-ir opt into exactly --format=json, once anywhere,
including before command; other spellings/formats, duplicates, unknown flags/missing
values are usage. doc remains Markdown-only. Handled JSON results emit exactly one
UTF-8 object+LF, stderr empty; write failure may use stderr and exits1. No progress/
NDJSON/prose mixture. Exact JSON flag makes handled usage JSON; otherwise usage uses
stderr. Prefix a leading-dash path with ./. command is first remaining argument,
empty if absent/non-UTF-8; preserve unknown UTF-8 names without executing them.

```json
{"format":"qleisli.result","version":1,"command":"check","outcome":"error",
 "diagnostics":[{"code":"ownership","severity":"error","message":"owner already consumed",
 "primary":{"path":"main.qli","start":27,"end":28,"line":2,"column":5},
 "related":[]}],"result":null}
```

All fields required. outcome ok/error; success has no error diagnostics, failure
has at least one/null result. severity error/warning; message explanatory, unstable.
primary may be null for usage/I/O/artifact-wide errors. related={message,location},
same location schema. Original unnormalized UTF-8 spans are half-open, empty EOF
allowed; line/column one-based Unicode scalars. Paths project-relative slash or std://;
non-UTF-8 path yields project/null, never lossy identity. Artifact related messages
carry json_pointer/null location, no invented source span.

Closed v1 codes: usage,project,parse,unknown_name,recursive_call,type_mismatch,arity,
ownership,effect,invalid_entry,unsupported,limit,invalid_ir,contract,capability,format,
simulation,random_source,numerical. Code/tag/version additions require format version.
Legacy CompileError snake_case categories remain (parser/load Project, existing contract
failures InvalidIr); new access/meaning checks use their defined categories. Capacity
runtime failure is limit, other runtime simulation. Exits0 success/2 usage/1 other;
typed retry exhaustion is successful trial result, not simulator error.

Success: check={verified:true}; run={distribution:[{bits:[bool,...],probability:number},...]}
lexicographic bit order; emit-ir={path:string}; verify-ir={verified:true,request_checked:bool};
sample below. Probabilities finite in[0,1]; endpoint clamp only within inclusive2^-40,
otherwise numerical/null/exit1. No distribution renormalization or positive-weight
cutoff; f64 residuals do not prove ideal support or weaken exact certification.

check_project_diagnostic/compile_project_diagnostic return Diagnostic{code,message,
primary?} through the same legacy checker. SourceLocation retains PathBuf, Span,
line/column from loaded provenance, never message parsing/later file read. Located
load failures retain spans; I/O/path/missing main null. Source failures have no related
locations. Ordinary unused manifest-key warnings use project/warning, outcome ok/exit0;
unknown metadata remains accepted. --qrate selects explicit source root, default
root-relative behavior unchanged. Legacy public error shapes/categories remain.


## Portable finite IR and evidence

Select **QIRF version 1**, a UTF-8 JSON interchange for the existing finite
RawProgram and its retained function-evidence DAG. CLI:

```text
qleisli emit-ir <project> --output=<new-file>
qleisli verify-ir <artifact> [--against=<request-file>]
```

Output uses exclusive creation and writes a complete temporary sibling before
atomic installation; an existing destination is an error. Verification never
loads source paths, accesses the network, runs a compiler/plugin, or executes
embedded code. An optional request is an independently chosen expected contract;
without it `request_checked` is false even when internal validity succeeds.
Artifact-supplied expectations cannot certify that the user asked for them.

The artifact has exactly `{format:"qleisli.finite-ir",version:1,profile:"finite-v0",
sources,programs,evidence,root,root_interface}`. Arrays are indexed by zero-based references.
`root` is a program index. Object key order/whitespace have no significance;
duplicate/unknown/missing keys, unknown tags, nonintegers in integer fields,
negative IDs, nonfinite numbers and ill-formed UTF-8 are rejected. Numbers used
for IDs/counts are decimal JSON integer tokens, not floats/exponents. IDs and
indices fit u32; gate/table values fit the narrower ranges below. No unchecked
conversion to host `usize` is allowed. String equality is exact Unicode scalar
equality without normalization; embedded sources preserve their UTF-8 bytes.

`sources` entries are `{path,text}`, with unique nonempty path labels, at most
4,096 bytes per path, no NUL, and at most 128 entries. Labels are identities,
never filesystem instructions. `programs` contains raw program objects.
`evidence` entries have `{signature,implementation,specification,identity}`:
the two programs are indices, `signature` is the full basis tree, and identity
is `{implementation:string,specification:string,sources:[source-index,...]}`.
Its source indices are unique and preserve the original identity snapshot order. Names obey the existing 4,096-byte
limit. Identity snapshots are checked binding metadata, not proof that source
lowering was correct.

`root_interface` is null or exactly `{input:BasisType,output:BasisType}`. A
non-null value describes the sole quantum input and sole quantum output of
`programs[root]`, which must have declared effect `unitary` and no classical
inputs/outputs. Import first verifies the raw program, then checks each tree's
bit count against its corresponding verified port, including the output token's
resolved shape and wire order. Bit leaves map left to right to the port's
ordered wires, first leaf least significant; retain every Unit node, tuple arity and nested
association. Both trees obey the existing depth-64 and 4,096-node type limits
as well as the transport limits. Invalid port/effect/width binding rejects the
artifact as `invalid_ir`; resource exhaustion is `limit`.

Export retains both exact trees from the type-checked frontend boundary or a
checked function contract for that same root implementation. Never reconstruct
them from bit counts, an unrelated nested evidence signature, or a request-file.
Use null for other root interfaces or when exporting legacy raw IR without
retained type information. Null permits ordinary IR verification but cannot
satisfy `--against`. The root index, both trees, ordered ports and complete
IR/evidence form one checked binding; any change requires revalidation. This
metadata is an untrusted declaration checked against the IR and, separately,
the user's request; it does not prove which source type was originally written.
The existing public RawProgram/QuantumPort records are unchanged: the new
transport envelope carries the root types.

The following encoding completely determines the finite payload. All named
record fields in [ir.rs](../src/ir.rs) are required with their current names.
This specification freezes their version-1 field set, recorded below; later
Rust fields are not silently added to the wire format.

| Type | Version-1 JSON representation |
| --- | --- |
| BasisType | `{"tag":"unit"}`, `{"tag":"bit"}`, `{"tag":"pair","left":T,"right":T}`, or `{"tag":"tuple","fields":[T,...]}` with at least three immediate fields; retain Unit nodes, exact arity and nesting. Two fields use `pair`; smaller `tuple` arrays reject. See the [0.2.0 type migration](tuple-shapes.md). |
| ID/index/bit count | Nonnegative integer; token/wire/classical IDs are distinct namespaces; a shape is `{"bits":n}` with n≤12 |
| QuantumPort | `{token,wires,shape}`; `wires` is an ordered array of wire IDs |
| RawProgram | `{quantum_inputs,classical_inputs,operations,quantum_outputs,classical_outputs,declared_effect}`; quantum inputs are ports, quantum outputs are token IDs, classical inputs/outputs are classical IDs |
| Effect / SingleGate / ScalarPhase | Strings `unitary/iso/observe`, `h/x/z/t`, `minus_one/eighth_turn` respectively |
| UnitaryStep | Tagged objects: `gate` with gate,target_index; `cnot` with control_index,target_index; `toffoli` with control_a_index,control_b_index,target_index; `scalar_phase` with phase |
| CircuitStep / BitControl | `{controls,action}` / `{index,when_one}` with boolean when_one |
| CircuitAction | `contract` with indices,evidence,adjoint; `hadamard` with target; `monomial` with indices,permutation,phases. Evidence is an evidence-array index, adjoint boolean; permutations use u16 and phases integers 0–7 |
| ProtectedBit / Control | `{region,index}` with region `source/ancilla`, index u8 / `{bit,when_one}` |
| ProtectedUse | `protected_gate` with bit,gate; `controlled_target_gate` with controls,target_index,gate; `controlled_phase` with controls,phase |
| TargetTransition | `{input,output}` token IDs |
| QuantumPhi | `{then_token,else_token,output,output_wires}` |
| ClassicalPhi | `{then_id,else_id,output}` |

Every tagged object above/below has a `tag` string in addition to its listed
fields. Arrays encode all Vec fields; booleans are JSON booleans. RawOp tags
and complete payload fields are:

| Tag | Fields |
| --- | --- |
| `certified_compute` | source,source_out,ancilla_wires,function,use_steps,logical_steps |
| `apply_unitary` | input,output,steps |
| `init0` | output,wire |
| `gate` | gate,input,output |
| `cnot` | control,target,control_out,target_out |
| `toffoli` | control_a,control_b,target,control_a_out,control_b_out,target_out |
| `quantum_if` | control,target,control_out,target_out,zero_ops,one_ops |
| `split` | input,left,right,left_bits |
| `join` | left,right,output |
| `lift_basis` | input,output,output_wires,table |
| `measure_z` | input,output |
| `reset` | input,output,fresh_wire |
| `discard` | input |
| `classical_const` | value,output |
| `classical_not` | input,output |
| `classical_xor` | left,right,output |
| `classical_and` | left,right,output |
| `classical_branch` | condition,then_ops,else_ops,quantum_phis,classical_phis |
| `compute_use_uncompute` | source,source_out,targets,ancilla_wires,function,use_ops |

`function`/`table` entries are u16. `use_steps`/`logical_steps`/`steps` are circuit
steps, `zero_ops`/`one_ops` are unitary steps, and branch arrays are RawOps.
Index ranges, arity, token freshness, shape compatibility, effect, table
totality/injectivity, axis order, exact phase and cleanup are checked by the
independent finite verifier, not inferred from successful JSON parsing.

Import performs bounded tokenization, schema/range preflight, graph validation,
then semantic checking. Construct edges program→referenced evidence and
evidence→implementation/specification programs; reject every cycle, invalid
reference and unused object/source. Share each checked evidence result once,
in topological order; do not recursively expand shared dependencies. Reconstruct
each FunctionEvidence with its ordinary exact checker, then independently
verify all referring raw programs and the root. Standalone CheckedContract
objects are not transported in QIRF1: retained SC claims are reconstructed
from their complete raw computed operation and rechecked. Nothing serializes
private checked fields, `Arc` identity, verified flags or a dense result as
authority. Export/import round trips may issue new evidence identities while
preserving complete structural binding and denotation.

The fixed transport limits are 16 MiB raw bytes, JSON nesting 128, 1,000,000
JSON values, 65,536 program/evidence objects combined, 1,000,000 total raw/step
nodes, graph depth 32 and 1 MiB total embedded source text. Bound each array
incrementally before allocation; reject deep inputs without recursive drop.
The stricter current semantic limits (six-bit evidence, 1,024 circuit steps,
1,000,000 expanded steps and 10,000,000 aggregate exact work per import) still
apply. The current 1 MiB identity budget counts implementation/specification
names for each distinct evidence entry, plus each referenced source path and
its exact text once per artifact. Repeated references to the same source index
spend no additional source-byte budget; duplicate indices within an identity
still reject. One path cannot label conflicting text. Import retains shared
immutable snapshots for identical ordered source-index sequences; changing
order or membership changes the snapshot. The ordinary evidence checker
revalidates every receipt, and its aggregate exact-work/storage budget still
applies. Export borrows metadata without materializing per-receipt source copies.
Counts are aggregate, not reset by each evidence entry. Exhaustion is
`limit`, not `invalid_ir`; both reject the artifact. These are limits on a new
format, not capacity changes to existing Rust constructors.

### Reconstructed finite unitary leaves

[finite_leaf](../src/interchange/finite_leaf.rs) is transitional Rust verification,
not Lean/hierarchy authority. UnitaryBoundary::new requires full legacy BasisType
and input/output QuantumPorts (owner, shape, ordered wires), same exact tree at both
ends, including zero-width Unit owner. Equal width does not convert Bit/Bits or trees.
check_unitary(payload,boundary,meaning,budget) freshly imports all QIRF1/2 and evidence,
requires declared/derived Unitary/no classical ports, matching retained trees/actual
final port, and extracts/checks the exact whole-space ordered matrix against independent
meaning including phase and isometry. Closed internal classical control is allowed;
six bits/dimension64 and arithmetic/circuit limits unchanged.

Caller Budget is shared across every import, receipt, extraction/equality/isometry,
not reset or allowed above10,000,000. Transport bounds still apply. Exhaustion limit,
malformed format, failed equation contract. CheckedUnitaryLeaf privately retains complete
immutable bytes/boundary/program/matrix; matches compares full bytes/structural values,
not addresses/digests (different whitespace changes binding). No serialized seal.
[Hierarchy](hierarchical-ir-spec.md) projects actual indexed requests/reconstructs fresh
obligations, including Fourier H under one budget; reader/native/decoder/production
correspondence remains explicit. Multi-owner/rectangular production integration is open.

### Exact finite matrix descriptions

[finite_matrix](../src/interchange/finite_matrix.rs) envelope exactly
{format:"qleisli.finite-matrix",version:1,domain:"zeta8-dyadic-v1",rows,cols,entries}.
Rows/cols1..64, exactly rows*cols row-major entries; rectangular descriptions are
valid but unary unitary leaf needs independently required square dimension.
Each scalar [a,b,c,d] means a+b*sqrt(2)+i*(c+d*sqrt(2)); each dyadic exactly
{numerator:string,denominator_bits:integer}, numerator/2^denominator_bits.
Canonical signed decimal i128:0 or nonzero decimal without leading zeros, optional
minus; no plus/negative-zero/whitespace/float. Exponents0..126 independently, zero
exponent0/nonzero odd numerator when exponent>0. Never rescale all four to one exponent.
Out-of-capacity numeral/exponent/dimension limit; malformed/noncanonical format.
Unknown fields/domains/versions/duplicate keys reject. Descriptions are not evidence.

encode deterministic JSON+LF. decode uses strict16MiB/depth128/million-value reader,
checks dimensions/count and charges4/entry before scalar construction, no refund on
failure, shared budget<=10M. No equation/isometry meaning proof from decoding.
check_serialized_unitary first bounds combined payload+description<=16MiB, decodes,
then invokes check_unitary. Private result retains complete description and payload;
matches binds both exact byte strings/boundary, work includes both stages. No receipt
or whole-root guarantee; hierarchy shares aggregate payload/work and rechecks indices.


### Independently supplied finite requests

A request-file is exactly `{format:"qleisli.request",version:1,signature,
meaning:{tag,table},source_snapshot}`. The signature is a basis tree; meaning
tag is `permutation` or `phase8`; table is the complete ordered u16 permutation
or 0–7 phase table. `source_snapshot` is null (no provenance requirement) or
the exact ordered array of `{path,text}`. `--against` requires a non-null,
validated `root_interface` whose input and output trees both equal the request
signature structurally, including Unit nodes, tuple arity and nested association. Missing
type information or either tree mismatch is `contract`, even if the bit counts
and operators agree; never fill in or replace root types from the request.
It also requires a closed unary unitary root (no classical inputs/outputs), exact
operator equality to the requested meaning and, if supplied, identical source
snapshots. Here “closed unary” means no free inputs beyond the one declared
quantum port, not a zero-input simulator entry point. It does not recompile
source or establish source adequacy. A valid but different contract is rejected.

Equal-width Bit/(Unit,Bit)/(Bit,Unit) requests differ. Either root-tree mismatch
or null interface rejects --against; a tree wider than its port is internally invalid.


M1's new meaning/evidence action uses **QIRF version 2**, with a distinct
profile `finite-meaning-v1`. It inherits all version-1 fields/rules and extends
evidence entries with a tag: `circuit` has the v1 fields; `meaning` has signature,
implementation,meaning,identity, where meaning is the request meaning above
and identity uses the declared meaning name as specification. All entries in
v2 require a tag. Import checks the meaning table and equality independently.
The checked v1→v2 adapter adds `circuit` tags and preserves `root_interface`
exactly, including null; v2→v1 rejects `meaning` entries
instead of disguising them as an unchecked circuit. Unknown versions fail.
Hierarchy requires another profile/version; it is never squeezed into v1/v2.

## Sampling and typed trials

Host sample_closed(VerifiedProgram,RandomSource,SampleLimits) returns Sample{bits,
execution_steps} or typed not-closed/limit/RNG/numerical/inconsistent-IR error, never
an error bit/live owner. Require no external ports/quantum outputs; retain exhaustive
API. RandomSource supplies fallible uniform u64 words, a caller premise.

Fresh normalized trajectory each call. Measurement sums p0 in ascending basis order,
draws u=(word>>11)*2^-53, selects0 iff u<p0, collapses/renormalizes; deterministic
observations also draw. Clamp only within2^-40 endpoints, else fail. After each
deterministic operation finite positive norm² must differ from1 by at most
2^-40+16*f64::EPSILON*actual_steps since previous normalization, including nested work,
not unused configured allowance. Before observation/after collapse/completion use
base2^-40; zero selected norm fails. Renormalization uses no draw/extra IR step.
Reset/discard hidden computational measurements remove old wire/optionally allocate
fresh zero, preserving partial-trace behavior; hidden draws follow program/ascending
wire order. Only selected classical arm executes. Runtime tolerance is not certified
forward error or evidence/hardware guarantee.

Defaults16 qubits(hard20),1,048,576 cells,1M executed steps/sample; charge primitives,
branch dispatch/repeated calls/hidden observations. One trajectory needs no ensemble
cap. CLI aggregate10M steps/all shots; failure returns no partial document.
sample <project> --shots=N --seed=S [--format=json], both canonical decimal required,
N1..1M, S0..2^64-1. One sequential splitmix64-v1 stream across fresh shots, seed=state:

```text
state = state + 0x9e3779b97f4a7c15
z = state
z = (z xor (z >> 30)) * 0xbf58476d1ce4e5b9
z = (z xor (z >> 27)) * 0x94d049bb133111eb
word = z xor (z >> 31)
```

Unsigned64 wrapping. Host may choose another uniform source; no implicit time seed.
Same backend/profile/program/seed reproduces trace, cross-platform rounding need not.
JSON {rng:"splitmix64-v1",seed:string,shots:[{bits,execution_steps},...],execution_steps:integer};
seed decimal text avoids client precision loss. Human mode one bitstring or() per shot.

run_trials(max_attempts,trial) invokes one-based callback -> Result<TrialDecision<T,R>,E>.
Decision Accepted(T)/Retry(R); result TrialRun Accepted{value,attempts,retries} or
Exhausted{attempts,retries}; TrialFailure InvalidLimit{requested,max} or
Execution{attempts_started,error,retries}. retries ordered{attempt,reason}. Invalid
bound invokes nothing; max1M; zero gives exhausted0. Acceptance stops, callback error
aborts without becoming retry. Each quantum callback freshly prepares/samples;
no collapsed-state reuse/secret seed change.

Bounded Shor client distinguishes invalid_candidate/odd_period/trivial_factor.
Profile2<=N<2^32,1<a<N,gcd(a,N)=1,m1..32. Enumerate convergents y/2^m in order,
denominators1<=r<N; require positive r and a^r modN=1, reduce by increasing prime
divisors for minimality, then even-period gcd tests. No successful denominator means
invalid_candidate. Validate1<p,q<N,p*q=N before reporting; continued fractions only
propose. Checked u128, Euclidean gcd/square-and-multiply, <=1M arithmetic iterations/
trial or limit error. Even-N/gcd prechecks report validated classical factors separately,
not quantum trials. General efficient arithmetic remains M4.


## Source input capacities and migration

The 0.2.0 CLI loader defaults to 1 MiB per UTF-8 `.qli` file and 16 MiB aggregate
across distinct canonical project files plus bundled modules, counting bytes
before decoding/normalization. Stream at most limit+1 bytes per file, rejecting
at the first excess; account files in existing deterministic path order.
I/O/UTF-8 errors remain project errors; size errors are `limit` and identify the
path and limit with no invented character span. Symlinks/canonical paths keep
the current project rules. Per-function source evidence retains its stricter
current 1 MiB snapshot limit, even if loading succeeds.

Add `--source-bytes=N --project-bytes=N` positive u64 overrides and a mutually
exclusive `--legacy-source-limits` restoring the current unbounded byte loader.
Host loading gains the analogous explicit policy object; retain the old loader
through an adapter selecting legacy policy. Arithmetic overflow is a limit
error. Overrides alter byte limits only, not parser/evidence/work limits.
The new default/restricted acceptance is MINOR; migration for old large
projects is explicit opt-in legacy loading or larger bounds. 0.1.5 adds no cap.

## Required conformance before shipping

| Gate | Positive and adversarial evidence required |
| --- | --- |
| X1 diagnostics | Golden success/usage/type/runtime JSON; Unicode and EOF spans; no mixed stdout; unchanged human check/run and exits; reject unknown/duplicate flags. |
| X2 interchange | Round-trip every RawOp/action, shared evidence DAG and exact root input/output trees (including Unit, tuple arity and nested association) through v1/v2; check requested meaning/provenance; reject cycles, dangling/unused entries, malformed tags/IDs, invalid root port/type binding, phase/output/source mutation and all limits, including deep-rejection destruction. |
| X3 independent trust | Import in a fresh process with no frontend/cache; mutate the root or requested target; accept matching typed identity requests, reject equal-width tree substitutions at either root port and null interfaces under `--against`; never infer types from requests; reject invalid contracts even when names/hashes match; document source-adequacy boundary. |
| X4 sampling | Deterministic basis states; seeded known generator words; Bell correlation, reset/discard marginal and feedback; independent statistical tests against finite exhaustive distributions with stated confidence/tolerance. No golden lucky random frequency. |
| X5 trials | Accept on first/later attempt, all retries, zero bound, injected RNG/runtime/numerical failure, invalid/odd periods, trivial gcds and checked factors; count preparation/attempts precisely. |
| X6 migration/capacity | Boundary byte sizes, multibyte UTF-8, many small files, bundle accounting, overflow and legacy override; old source/IR behavior preserved through explicit adapters. |

Executed evidence is retained with [CLI tests](../tests/cli_json.rs),
[location tests](../tests/diagnostics.rs), [decoder tests](../scripts/test_cli_json.py)
and the immutable 0.2.0 release record linked above. This specification is not a
fresh test report or source-adequacy theorem.


## 0.2.0 host API mapping

[`interchange::export`](../src/interchange/mod.rs) accepts a `VerifiedProgram`,
optional retained `RootInterface`, and `Version::V1`/`V2`.
`export_with_meanings` retains explicitly supplied sealed `MeaningEvidence`
receipts as v2 meaning entries; ordinary export retains their already checked
canonical target circuits. `convert` checks the input and preserves source
ordering and exact root types; it rejects a v2 meaning entry when targeting v1.
`import(bytes, request)` reconstructs all receipts and returns the verified
root, retained interface, `request_checked`, and charged exact work.

The CLI emitter currently exports the closed observation entry as QIRF2, with
a null root interface. Such an entry cannot satisfy a unary unitary request;
typed unitary producers use the Rust exporter and retain their exact trees.
`verify-ir` accepts both specified versions and has no frontend dependency in
its execution path. No source-adequacy theorem is claimed by either adapter.

[`sample_closed`](../src/sim/sampling.rs), `RandomSource`, `SampleLimits`,
`SampleError` and `SplitMix64` implement X4; [`run_trials`](../src/host.rs) and
the [bounded factoring helpers](../src/host/factoring.rs) implement X5.
[`SourcePolicy`](../src/frontend/project.rs) and policy-bearing project/check/
compile functions implement X6. Existing host entry points select `Legacy`.
These are host APIs, not new sealed `.qli` operations or bundled definitions.
Their future shipping still requires the remaining release validation and a
compatibility-based release decision; reduced acceptance in X6 requires MINOR.
X1 diagnostic transport alone is not portable IR or evidence.
