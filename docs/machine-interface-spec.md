# Selected M1 machine interfaces

Status: **specified, unimplemented** (2026-09-27). These are independently
shippable MINOR slices of [M1](next-minor-spec.md), not 0.1.5 APIs. Formats below
have their own versions; product/package versions never change their meaning.
Current `check`/`run`, Rust IR and exhaustive reference simulation stay intact.

## Diagnostics

Add the opt-in flag `--format=json` to `check`, `run`, `sample`, `emit-ir` and
`verify-ir`. Flags may precede/follow positional arguments; duplicates, unknown
flags and missing values are usage errors. With this flag, stdout is exactly
one UTF-8 JSON object plus LF, also on failure. Diagnostic prose is never mixed
into stdout. Stderr is empty for handled results; an OS-level failure to write
the JSON document may use stderr and exits 1. No NDJSON/progress stream is used.
Human mode for the two existing commands preserves existing output/exit rules.

```json
{"format":"qleisli.result","version":1,"command":"check","outcome":"error",
 "diagnostics":[{"code":"ownership","severity":"error","message":"owner already consumed",
 "primary":{"path":"main.qli","start":27,"end":28,"line":2,"column":5},
 "related":[]}],"result":null}
```

All displayed fields are required. `outcome` is `ok` or `error`; success has
no error diagnostic, failure has at least one and a null result. Severity is
`error` or `warning`. `message` is explanatory text, not a stable API. A primary
location may be null for usage, I/O or artifact-wide errors. Related entries
are `{message,location}` with the same location schema. Spans are half-open
UTF-8 byte offsets into the original unnormalized source; empty EOF spans are
allowed. Line/column are one-based Unicode scalar positions, matching the
current frontend. Paths are project-relative with `/`, or `std://` for bundled
sources. Non-UTF-8 filesystem paths produce `project` with null location;
never lossy-encode an identity. Artifact errors use `json_pointer` in a related
entry's message when no source location exists; they do not invent source spans.

Version 1 codes are `usage`, `project`, `parse`, `unknown_name`, `recursive_call`,
`type_mismatch`, `arity`, `ownership`, `effect`, `invalid_entry`, `unsupported`,
`limit`, `invalid_ir`, `contract`, `capability`, `format`, `simulation`,
`random_source`, and `numerical`. Existing CompileError codes map to their
snake_case spellings; parser/load, new access/contract and runtime errors map
to the corresponding additional codes. CLI exit is 0 for successful command
execution, 2 for usage and 1 for other failure. Retry exhaustion is a successful
trial-run result, not a simulator error; clients inspect its typed outcome.
Version/tag/code additions require a new format version for this closed schema.

Success result schemas: `check` is `{verified:true}`; `run` is
`{distribution:[{bits:[bool,...],probability:number},...]}` in lexicographic
bit-vector order; `emit-ir` is `{path:string}`; `verify-ir` is
`{verified:true,request_checked:bool}`; `sample` is specified below. Probabilities
are finite numbers in [0,1]; reference floating output is not an exact proof.
The envelope only reports the check actually performed.

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
ordered wires, first leaf least significant; retain every Unit node and pair
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
| BasisType | `{"tag":"unit"}`, `{"tag":"bit"}`, or `{"tag":"pair","left":T,"right":T}`; retain Unit nodes |
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
names and source path bytes as well as source text. Counts are aggregate, not
reset by each evidence entry. Exhaustion is
`limit`, not `invalid_ir`; both reject the artifact. These are limits on a new
format, not capacity changes to existing Rust constructors.

A request-file is exactly `{format:"qleisli.request",version:1,signature,
meaning:{tag,table},source_snapshot}`. The signature is a basis tree; meaning
tag is `permutation` or `phase8`; table is the complete ordered u16 permutation
or 0–7 phase table. `source_snapshot` is null (no provenance requirement) or
the exact ordered array of `{path,text}`. `--against` requires a non-null,
validated `root_interface` whose input and output trees both equal the request
signature structurally, including Unit nodes and pair association. Missing
type information or either tree mismatch is `contract`, even if the bit counts
and operators agree; never fill in or replace root types from the request.
It also requires a closed unary unitary root (no classical inputs/outputs), exact
operator equality to the requested meaning and, if supplied, identical source
snapshots. Here “closed unary” means no free inputs beyond the one declared
quantum port, not a zero-input simulator entry point. It does not recompile
source or establish source adequacy. A valid but different contract is rejected.

For example, a one-bit identity root declared with input/output `Bit` satisfies
an identity request on `Bit`, but rejects identity requests on `(Unit,Bit)` or
`(Bit,Unit)`. An identity root declared with `(Unit,Bit)` at both ports instead
satisfies the matching `(Unit,Bit)` request. Changing only its output tree to
`Bit` rejects that request; replacing the interface with null also rejects it.
A declared two-bit tree on that one-bit root is internally invalid even without
`--against`. Equal matrix dimensions never establish equality of type trees.

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

Add `sample_closed(program, random, limits) -> Result<Sample, SampleError>`
as a **host Rust API**, taking a VerifiedProgram, a mutable fallible random
source returning uniform u64 words, and explicit limits. Sample owns
`bits: Vec<bool>` in the same output order as `run_closed` and
`execution_steps: u64`. It returns no live quantum owner. The input program
must have no external quantum/classical inputs and no quantum outputs.
Errors distinguish not-closed, limit, random-source failure, numerical failure
and inconsistent verified IR. No error is returned as an ordinary outcome bit.
Keep the existing exhaustive simulator/API unchanged.

Use one normalized pure-state trajectory, starting from empty state on every
call. At measurement, compute p0 by ascending basis index, draw
`u=(word>>11)*2^-53`, select zero iff u<p0, collapse and renormalize the chosen
branch. Clamp a probability outside [0,1] only within 2^-40; otherwise return
numerical failure. Require finite amplitudes and |norm²−1|≤2^-40 before every
observation and at completion; renormalize within tolerance, never continue
from a zero-norm selected branch. Deterministic observations still consume a
word. Reset/discard use a hidden computational-basis measurement, then remove
the old wire and optionally allocate fresh zero; this reproduces the ensemble
partial trace, including entangled inputs. Consume hidden draws in program and
ascending wire order. Runtime classical branches execute only the selected arm.
This sampling algorithm is approximate reference execution, not a proof of
exact semantics or a guarantee of hardware distributions.

Defaults: max live qubits 16 (hard maximum 20), amplitude cells 1,048,576,
execution steps 1,000,000 per sample. Charge each executed primitive/branch
dispatch and each repeated/called step, including hidden observations; symbolic
counts never make execution free. No ensemble-component limit is needed for
one trajectory. Aggregate CLI work is at most 10,000,000 executed steps across
all shots; error atomically with no partial success document if exceeded.

CLI syntax is `qleisli sample <project> --shots=N --seed=S [--format=json]`.
Both are required: 1≤N≤1,000,000 and 0≤S<2^64, decimal canonical integers.
Use a single sequential generator stream across fresh shots. Generator profile
`splitmix64-v1` is specified by this exact unsigned-64 wrapping algorithm:

```text
state = state + 0x9e3779b97f4a7c15
z = state
z = (z xor (z >> 30)) * 0xbf58476d1ce4e5b9
z = (z xor (z >> 27)) * 0x94d049bb133111eb
word = z xor (z >> 31)
```

Seed initializes state directly. The host API may supply a different uniform
source; the CLI has no implicit time-based seed. Same seed/profile/program and
numeric backend reproduce a trace; cross-platform floating rounding can change
a boundary decision and is not promised bit-for-bit. JSON result is
`{rng:"splitmix64-v1",seed:string,shots:[{bits,execution_steps},...],
execution_steps:integer}`; seed is decimal text to avoid JSON-client precision
loss. Human output is one bitstring (or `()`) per shot. This is an actual draw,
not returning every branch of `run_closed`.

Provide the independent host combinator `run_trials(max_attempts, trial)`.
The callback receives a one-based attempt index and returns
`Result<TrialDecision<T,R>, E>`, where TrialDecision is `Accepted(T)` or
`Retry(R)`. R is the caller's typed retry reason. Result is
`Result<TrialRun<T,R>, TrialFailure<R,E>>`; TrialRun is
`Accepted{value,attempts,retries}` or `Exhausted{attempts,retries}`.
TrialFailure is `InvalidLimit{requested,max}` or
`Execution{attempts_started,error:E,retries}`. InvalidLimit invokes no callback.
`retries` is an ordered
list of `{attempt,reason}`. A callback error aborts immediately and is never
counted as a retry; acceptance stops immediately. Zero attempts yields
Exhausted with zero attempts without invoking the callback. Maximum accepted
bound is 1,000,000. Each quantum callback must invoke fresh preparation/sampling;
the combinator does not reuse a collapsed state or secretly choose a new seed.

The first Shor host integration keeps `invalid_candidate`, `odd_period`, and
`trivial_factor` as distinct retry reasons. Before reporting a period, check
r>0, a^r mod N=1 and minimality by prime-divisor reduction of r. Before reporting
factors check 1<p,q<N and p*q=N with checked arithmetic; an unverified continued
fraction denominator is only a candidate. Select the bounded reference host
profile 2≤N<2^32, 1<a<N, gcd(a,N)=1 and 1≤m≤32. Enumerate convergents of y/2^m
in order, test denominators 1≤r<N, reduce successful r by trial-dividing its
prime factors in increasing order, then apply the standard even-r gcd tests.
No successful denominator yields invalid_candidate; no fabricated period.
Arithmetic uses checked u128, Euclidean gcd and square-and-multiply modular
power. At most 1,000,000 arithmetic loop iterations per trial; exhaustion is
an execution limit error. Classical prechecks (even N/nontrivial gcd) report
validated classical factors separately, without claiming a quantum trial.
This specifies integration behavior; general efficient number theory is M4.

## Source input capacities and migration

The future loader defaults to 1 MiB per UTF-8 `.qli` file and 16 MiB aggregate
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
| X2 interchange | Round-trip every RawOp/action, shared evidence DAG and exact root input/output trees (including Unit and pair association) through v1/v2; check requested meaning/provenance; reject cycles, dangling/unused entries, malformed tags/IDs, invalid root port/type binding, phase/output/source mutation and all limits, including deep-rejection destruction. |
| X3 independent trust | Import in a fresh process with no frontend/cache; mutate the root or requested target; accept matching typed identity requests, reject equal-width tree substitutions at either root port and null interfaces under `--against`; never infer types from requests; reject invalid contracts even when names/hashes match; document source-adequacy boundary. |
| X4 sampling | Deterministic basis states; seeded known generator words; Bell correlation, reset/discard marginal and feedback; independent statistical tests against finite exhaustive distributions with stated confidence/tolerance. No golden lucky random frequency. |
| X5 trials | Accept on first/later attempt, all retries, zero bound, injected RNG/runtime/numerical failure, invalid/odd periods, trivial gcds and checked factors; count preparation/attempts precisely. |
| X6 migration/capacity | Boundary byte sizes, multibyte UTF-8, many small files, bundle accounting, overflow and legacy override; old source/IR behavior preserved through explicit adapters. |

These tests have not been implemented or executed in the documentation release.
Formats, API contracts, failure policies and limits are selected here; shipping
requires implementation, validation and a new MINOR release record.
