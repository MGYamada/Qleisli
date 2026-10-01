# M1.1: bounded OpenQASM 3 and QIR connections

Status: **implemented bounded terminal connections**, including Rust adapters,
the structured CLI, Python orchestration and optional PyQIR input. M1.1 names a
development submilestone, not a product version. Adaptive circuits, general
translation proofs and bundled native wheels remain open. These adapters use
the existing finite Rust verifier; they add no language form or acceptance rule.

## Host interface and trust boundary

The additive Rust module `qleisli::interop` provides:

```text
import_openqasm3(source: &str) -> Result<VerifiedProgram, InteropError>
export_openqasm3(program: &VerifiedProgram) -> Result<String, InteropError>
export_qir_base(program: &VerifiedProgram) -> Result<String, InteropError>
```

These are host adapters, not `.qli` forms or sealed quantum operations.
Import parses a declared subset, reconstructs logical ownership, lowers to
existing IR and calls the same independent `verify` as every other producer.
There is no external-file execution, include lookup, network access, imported
proof authority or new verifier case. `stdgates.inc` selects the fixed meanings
below and is never loaded from disk. A private terminal-circuit description
connects the adapters; it is not a new trusted IR or public certificate.

`InteropError` distinguishes `Parse`, `Unsupported`, `Limit` and `InvalidIr`,
with explanatory text, an optional original UTF-8 byte `Span` for imports and
an optional zero-based raw operation index for exports. These locations are
not invented when failure concerns the whole artifact. No successful artifact
or partial output is returned on failure. The structured CLI below and
`cargo run --example interop -- ...` provide host callers.

## Structured CLI and Python

`qleisli interop ACTION INPUT --input=FORMAT` emits one version-1
`qleisli.result` JSON envelope. Actions are `check`, `run`, `sample`, `emit-ir`,
`emit-qasm` and `emit-qir`; formats are `qasm`, `qirf` and `qli`.
Input is a file, stdin `-` for qasm/qirf, or a source project for qli.
Sampling requires `--shots=N --seed=S` and uses the existing bounds, SplitMix64
and a fresh state per shot. Exports return `result.text`. Success exits 0,
processing failures 1 and usage failures 2. Input bounds are 1 MiB for QASM,
16 MiB for QIRF and the existing source-project policy for QLI.

Artifact errors retain JSON pointers in `related`. OpenQASM spans retain
original UTF-8 byte offsets and one-based line/Unicode-column coordinates,
with CRLF counted once; stdin uses filename `-`. Unlocated errors keep
`primary: null`. See [CLI regressions](../tests/connections.rs).

The [Python host](../python/README.md) provides `Client`, `Program` and
`QleisliError`. `from_openqasm`, `from_qir`, `from_ir` and `compile_project`
construct programs; checking, execution, sampling and export freshly invoke
the Rust boundary. A Python object never supplies acceptance authority.
The host needs Python 3.11+ and a separately installed matching Rust executable.
Pure host wheels do not bundle that executable or LLVM.

## Optional QIR input

The isolated [reader](../python/qleisli/_qir.py) uses pinned **PyQIR 0.12.5**
(MIT) to parse text/bitcode and verify LLVM. It accepts one closed entry with
static counts at most twelve, an acyclic unconditional block chain, the terminal
QIS vocabulary below, Z measurements and one ordered result array. It validates
signatures, module/profile flags, measurement attributes, pointer identities,
initialization placement, measurement/result uniqueness and output order.
Traversal uses LLVM block identity, including unnamed blocks.

Reject additional definitions, dynamic resources, loops, conditional or
unvisited blocks, unknown calls/custom QIS bodies, post-measurement gates,
measured-wire/result reuse, unsupported output structures, assembly, mutable
globals and unknown semantic attributes. Parsing is capped at 1 MiB with
bounded function/block/instruction counts. Imported code is never executed.
The validated slice becomes canonical QASM with explicit reset/output order;
Rust reconstructs logical owners and independently checks the IR. Unrecorded
measured systems and other terminal wires are explicitly discarded.

LLVM validity, profile validation, IR acceptance and translation correctness
are distinct. Reader wheels and their LLVM/dependency notices belong to PyQIR;
default Rust builds need neither Python nor LLVM. The
[connection harness](../scripts/test_connections.py) and
[retained validation](../tests/fixtures/interop/connections-validation.json)
cover text/bitcode, output order, invalid signatures/CFG/resources, phase,
structured errors, isolated host installation and seeded sampling.

## Terminal profile v1

The profile is a **closed observing computation**: all qubits start in zero,
a fixed unitary gate sequence precedes all measurements, and the result is an
ordered vector of measured bits. No live quantum output crosses the root.
Unrecorded terminal qubits/results are traced out, never released as pure zero.
The target platform must supply zero initialization and the stated QIS.
OpenQASM declarations alone leave states undefined, so the adapter requires an
explicit initialization prefix: exactly one `reset` of every declared qubit,
before any gate or measurement. It lowers this fresh preparation to `Init0`.
Export writes this reset prefix; no default device state is assumed.

- At most 12 qubits, 12 recorded bits, 4,096 expanded gates and 65,536 input
  tokens; at most 1 MiB UTF-8 OpenQASM text. Export visits at most 65,536 raw
  operations and applies the same gate/qubit/output bounds. These are new
  adapter limits; existing Rust and `.qli` limits are unchanged.
- Physical indices are zero based. An operand's first bit is the least
  significant axis when a multiwire action is lowered. CNOT's first operand
  controls the second; CCX's first two control the third.
- Each qubit is measured at most once. Once any measurement occurs, no further
  quantum gate or declaration is admitted. Measurements on disjoint terminal
  wires commute, so output order may differ from measurement order.
- Import returns classical bits in declaration order, then ascending register
  index. Every declared bit is assigned exactly once. Export uses the raw
  `classical_outputs` order and rejects repeated output IDs; it never infers
  output order from physical qubit indices.
- Unknown gates, angles, gate modifiers, user gate bodies, calibration, host
  calls, loops, classical arithmetic/feedback, mid-circuit reset and post-measurement reuse
  are unsupported. They are rejected, not erased, rounded or executed.

The accepted exact gates are H, X, Y, Z, S, S-adjoint, T, T-adjoint, CX, CZ,
SWAP and CCX. H has its standard real matrix; X swaps labels; Y maps
`|0> -> i|1>` and `|1> -> -i|0>`; Z/S/T have diagonal phases
`(1, ζ8^4)`, `(1, ζ8^2)`, `(1, ζ8)` respectively. Adjoints negate the
exponents modulo eight. CX/CCX flip only the last operand when all preceding
controls are one; CZ negates `|11>`; SWAP exchanges axes. Global phase is
preserved exactly in these gate definitions. No Rz-to-phase substitution or
phase quotient is permitted. Uncontrolled nontrivial scalar phase remains unsupported; it is never
quotiented away. Conditional eighth-turn scalar phases are expanded into
phase gates on their controls, with clean synthesis workspace when needed.

Import desugars these gates into `ApplyUnitary` Hadamard/monomial actions,
using explicit Join/Split ownership transitions for multiwire operands.
Initialization and observation use existing Init0/MeasureZ/Discard operations.
No raw-only QuantumIf or protected-use variants are introduced by the importer.

Export accepts closed verified programs built from Init0, Gate, Cnot,
Toffoli, Split, Join, the supported exact ApplyUnitary steps, terminal MeasureZ
and terminal Discard. Allocations before observation may move to the beginning
because each fresh zero wire has no earlier use; no physical ID is reused.
Export additionally expands negative controls with X conjugation, single-control
H, and one-axis diagonal eighth-turn phases. Even controlled phases use an exact
CX/phase decomposition; odd controlled phases compute the conjunction into
clean workspace, apply the phase and undo the conjunction. Workspace is reused
only after restoration, starts in zero, and is included in the 12-qubit target
limit and QIR required_num_qubits/OpenQASM declarations. This is backend
workspace, not a new source owner or a general realizability theorem. QFT2 and
QFT3 now export; QFT3 uses one extra clean target qubit.

Adjacent single-qubit phase gates on the same physical operand are folded
modulo eight: S/S-adjoint/T-adjoint export as short target words. No commuting
across other gates, controlled-phase erasure or projective equality is used.
IR T counts still describe the literal finite-v0 word; they are not minimal
physical non-Clifford costs. No Resource Safety certificate is issued.

Equal-width LiftBasis tables are admitted only when every row is exactly an
axis permutation, including identity. The output owner ordering is tracked
without inventing a physical SWAP. Other lifts, QuantumIf, contracts, certified cleanup, classical
operations/branches and other IR constructors receive Unsupported. Valid IR
does not imply that this target profile can represent it.

## OpenQASM input and output

Use the [OpenQASM 3.1 language](https://openqasm.com/versions/3.1/) as the
versioned reference for the common 3.0/3.1 subset. Require an explicit
`OPENQASM 3.0;` or `OPENQASM 3.1;` header. Export writes `OPENQASM 3.0;`.
Declarations are scalar or fixed positive-size `qubit`/`bit` arrays, followed
by initialization resets, gates and terminal measurements. Declarations after
the first reset are rejected. Resets accept scalar/indexed or whole-array
operands and each qubit must occur exactly once. Sizes and indices are canonical decimal
integers. Identifiers are ASCII and cannot shadow language keywords, constants or
standard-library gate names, including unsupported gates. Whitespace is space,
tab, CR or LF; the header version is a contiguous token.
Comments are `//` and non-nested `/* ... */`; offsets refer to original text.

The only include is a single `include "stdgates.inc";`, before declarations.
It is required when a standard gate is used. Gate operands must be scalar
qubits or explicitly indexed array elements; broadcasting is unsupported.
Accept `c = measure q;` and `measure q -> c;` for matching scalar/array shapes,
and `measure q;` with a hidden result. Whole-array measurement expands in
ascending index order. Registers and their indices are range/type checked.
Unmeasured qubits are explicitly discarded in imported IR at root exit.
Hidden terminal measurement results are also lowered to observing discard:
the measured subsystem is traced out, no subsequent operation uses it, and
the reduced state of the remaining subsystem is the same. This equivalence
does not authorize erasing measurements whose results or qubits are reused.

For example, accept Bell preparation with two distinct qubits and terminal
measurements. Reject `cx q[0], q[0];`, a second write to `c[0]`, a gate after
measurement, an arbitrary include, a user-defined `h`, or an unsupported angle.
Export canonically uses one qubit array and one result array when nonempty,
and an explicit `reset q;` before gates;
unrecorded qubits are traced out at closed-program termination. It does not
claim general source-to-source preservation or carry Qleisli certificates.

## QIR Base output

Pin the QIR specification to commit
`f5647346542d5a65225c3eb349847fe4df01d1b2`,
[Base Profile](https://github.com/qir-alliance/qir-spec/blob/f5647346542d5a65225c3eb349847fe4df01d1b2/specification/profiles/Base_Profile.md).
Select **QIR 2.0**, opaque pointers, static qubit/result IDs and LLVM 17-compatible
textual IR. The initial writer emits `.ll` text; a downstream standard LLVM
assembler produces bitcode. Native execution and device submission are absent.

The entry is `i64 @main()` with entry/body/measurements/output blocks, runtime
initialization, unconditional branches and `ret i64 0`. Declare required
qubit/result counts, `base_profile`, a versioned Qleisli output-label scheme,
QIR 2.0 module flags and false dynamic-management flags. Measurement uses
`mz__body(ptr, ptr writeonly)` marked `irreversible`. Every output recording
call has its own non-null, null-terminated global label; record one array of
the requested measured bits in their original output order.

The target QIS contract uses `__quantum__qis__h/x/y/z/s/t__body`,
`s/t__adj`, `cnot/cz/swap/ccx__body` with the exact gate meanings above,
and `mz__body`. All return void. Supporting Base Profile alone does not
establish support for this QIS; targets must provide these symbols/meanings.
No arbitrary external symbols are accepted and no target optimizer inherits
Qleisli evidence from this text. Unrecorded terminal wires are traced out at
entry termination under the closed-output contract.

The production crate gains no LLVM/Python dependency. Standard LLVM parsing and
verification are independent validation gates for exported fixtures. PyQIR
is evaluated as the future reader bridge; it is not replaced by an ad-hoc
LLVM parser. QIR import must still validate profile flags, declarations, entry
CFG, QIS signatures/attributes, identities, limits and ownership independently.

## Acceptance and remaining gates

M1.1-A covers the shared bounded profile, OpenQASM import/export and QIR output.
Require independent source fixtures, invalid/aliased/reused IDs, unknown names,
unsupported phases, output reordering, resource bounds, Bell/interference
distributions and exact gate mappings. Parse exported OpenQASM with an independent
reference parser and QIR with LLVM, then inspect profile/QIS structure. Round
trips and numeric histograms alone do not validate open-operation phase.

The terminal QIR reader is implemented; adaptive measurement/reset/reuse with
instrument correspondence remains open. Bundled native wheels, general .qli
export, portable Qleisli evidence, all M1 N/X gates and M2 scaling are separate.
These adapters add no soundness theorem and do not shrink the trusted core.

## Reproduction and reader decision

```sh
cargo run --example interop -- qasm-check tests/fixtures/interop/bell.qasm
cargo run --example interop -- qasm-run tests/fixtures/interop/bell.qasm
cargo run --example interop -- qasm-to-qir tests/fixtures/interop/bell.qasm
cargo run --example interop -- qli-to-qasm tests/fixtures/interop/terminal
cargo build --example interop
python3 -m venv /tmp/qleisli-interop-validation
/tmp/qleisli-interop-validation/bin/pip install -r scripts/interop-validation-requirements.txt
/tmp/qleisli-interop-validation/bin/python scripts/test_interop_external.py target/debug/examples/interop --llvm-as llvm-as --opt opt
```

The `.qli` modes take a project directory; the QASM modes take one UTF-8 file.
All successful output goes to stdout. `qasm-canonical` exercises QASM export;
`qli-to-qir` exercises the same QIR writer after ordinary source compilation.
Existing examples containing lifts or retained contracts can verify but fail
this limited export profile; the dedicated terminal fixture uses supported IR.

Validation-only dependencies are OpenQASM's reference Python parser **1.0.1**
(Apache-2.0) and ANTLR Python runtime **4.13.2** (BSD-3-Clause). They are installed
separately, not vendored or linked into the Rust package. LLVM retains its own
Apache-2.0-with-LLVM-exception licensing. Local QIR assembly/verification used
**LLVM 22.1.6**; the dedicated CI job passed with **LLVM 18** on Ubuntu 24.04
in [implementation CI](https://github.com/MGYamada/Qleisli/actions/runs/36382687389). LLVM 17-compatible textual syntax is the target, not a claim
that LLVM 17 was executed. Native device/runtime execution remains untested.

[PyQIR's reader API](https://www.qir-alliance.org/pyqir/api/pyqir.html#pyqir.Module.from_ir)
provides the module/bitcode/verification and inspection APIs used by the optional
reader. The pinned dependency and checked subset above define the current scope.

Primary initialization reference: [OpenQASM 3.1 quantum types](https://openqasm.com/versions/3.1/language/types.html#qubits)
defines declarations as initially undefined; the explicit reset requirement
above is necessary to establish this adapter's closed zero-input contract.
