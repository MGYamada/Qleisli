# M1.1: bounded OpenQASM 3 and QIR connections

Implemented terminal host adapters, structured CLI/Python and optional PyQIR input. Rust independently verifies every producer; adaptive/general translation proofs remain open.

## Host interface and trust boundary

interop::import_openqasm3(&str), export_openqasm3(&VerifiedProgram), export_qir_base(&VerifiedProgram) return verified program/text or InteropError Parse/Unsupported/Limit/InvalidIr. Imports retain original UTF-8 spans; exports optional zero-based raw index. Failures return no partial output. No include-file/network/code execution; stdgates.inc selects fixed meanings. The private terminal description supplies no acceptance authority.

## Structured CLI and Python

`qleisli interop ACTION INPUT --input=qasm|qirf|qli` always emits the version-1 [result envelope](machine-interface-spec.md). Actions check/run/sample/emit-ir/emit-qasm/emit-qir; qasm/qirf file or stdin `-`, qli project. Sample requires shots/seed and fresh states; exports result.text. Exits0/1/2. Limits QASM1 MiB/QIRF16 MiB/QLI source policy. Original spans, CRLF/Unicode coordinates and artifact JSON pointers retained. [Python](../python/README.md) Client/Program/QleisliError invoke a matching separately installed Rust executable; Python3.11+, no bundled executable/LLVM.

## Optional QIR input

[_qir](../python/qleisli/_qir.py) uses PyQIR0.12.5 to parse/verify LLVM text/bitcode, never execute it. One closed entry, static counts<=12, acyclic unconditional block chain, fixed QIS, terminal measurements and one ordered result array. Check signatures/module/profile flags, attributes, block/pointer identities, initialization and measurement/result uniqueness/order. Reject extra definitions, dynamic resources, loops/conditional/unvisited blocks, unknown/custom calls, reuse, output structures, assembly/mutable globals/unknown semantic attributes. Input1 MiB and bounded functions/blocks/instructions. Canonical QASM adds explicit reset/discard; Rust checks ownership independently. LLVM validity is not translation correctness.

## Terminal profile v1

Closed observing computation: every qubit fresh zero, fixed unitary sequence before all measurements, ordered classical output, no surviving owner. OpenQASM declarations are undefined states: require exactly one reset of each declared wire before gates/measurements. Unrecorded systems/results are explicitly traced out.

Bounds12 qubits/12 recorded bits/4096 expanded gates/65,536 tokens/1 MiB text; export<=65,536 raw visits and same output bounds. Physical indices zero-based; first multiwire operand low axis, CX first controls second, CCX first two control third. At most one measurement/wire; after observation no gates/declarations. Each declared result bit assigned once; import outputs declaration then register-index order, export raw classical_outputs order, no duplicates.

Exact H,X,Y,Z,S,Sdg,T,Tdg,CX,CZ,SWAP,CCX. Y|0>=i|1>,Y|1>=-i|0>; Z/S/T diagonal(1,zeta8^(4/2/1)), adjoints negate exponents; CX/CCX controlled XOR, CZ negates11. No phase quotient/RZ substitution/rounding. Uncontrolled nontrivial scalar unsupported; conditional scalars synthesize phases on controls.

Import uses existing ApplyUnitary Hadamard/monomial plus Join/Split/Init0/MeasureZ/Discard. Export supports those terminal operations and equal-width LiftBasis only when every row is an axis permutation. Fresh init can move before observation; no physical ID reuse. Negative controls use X conjugation; single-controlled H and even eighth-phase use exact decomposition, odd phases compute a conjunction into clean workspace then uncompute. Workspace counts toward12 and declarations/QIR counts, reused only after restoration. QFT2/3 export, QFT3 one extra workspace wire. Fold only adjacent same-wire phases modulo8, no commuting across gates. Other lifts/QuantumIf/contracts/cleanup/classical operations or unsupported gates/angles/modifiers/host/loops/feedback/calibration reject Unsupported. No resource certificate follows from counts.

## OpenQASM input and output

Header OPENQASM3.0/3.1 required, exporter3.0. ASCII names/canonical positive array sizes/indices; cannot shadow keywords/constants/standard gate names. Space/tab/CR/LF, contiguous header version, line/non-nested block comments. At most one include "stdgates.inc" before declarations, required for standard gates; no disk lookup. All declarations precede resets. Reset scalar/index/whole-array exactly once/wire. Gates use explicit scalar/index operands, no broadcast. `c=measure q`, `measure q->c` require matching scalar/array shapes; whole-array ascending order. `measure q` hides result via observing discard. Export one qubit/result array when nonempty plus reset prefix. Reject aliases/repeated assignments/gates after measurement. See [fixtures](../tests/fixtures/interop/bell.qasm).

## QIR Base output

QIR2.0, opaque pointers, LLVM17-compatible text, static IDs; [Base Profile](https://github.com/qir-alliance/qir-spec/blob/f5647346542d5a65225c3eb349847fe4df01d1b2/specification/profiles/Base_Profile.md) commit f5647346542d5a65225c3eb349847fe4df01d1b2. Entry i64 @main, initialize, unconditional entry/body/measurements/output, return0. Required counts/base_profile/versioned labels/2.0 flags, false dynamic flags. mz__body(ptr,ptr writeonly) irreversible; one ordered result array with distinct non-null terminated labels. Target must implement exact void h/x/y/z/s/t__body, s/t__adj, cnot/cz/swap/ccx__body and mz__body; Base support alone is insufficient. Unrecorded wires traced out at termination. No runtime/device submission or inherited evidence.

## Acceptance and remaining gates

M1.1-A: independent fixtures/parser/LLVM, aliases/reuse/unknowns/phases/output-order/bounds, Bell/interference and exact mappings. Roundtrips/histograms alone do not validate open phase. Terminal reader implemented; adaptive instruments/native wheels/general export/all M1/M2 gates remain separate.

## Reproduction and reader decision

`cargo run --example interop -- qasm-run tests/fixtures/interop/bell.qasm`; qasm-check/qasm-canonical/qasm-to-qir take files, qli-to-qasm/qli-to-qir take projects. [External runner](../scripts/test_interop_external.py) uses separately installed parser1.0.1/ANTLR4.13.2/LLVM; dependency notices remain upstream. [Connections](../scripts/test_connections.py) covers optional PyQIR text/bitcode. Local LLVM22.1.6/CI18 observations are not LLVM17 execution or device validation. [OpenQASM initialization](https://openqasm.com/versions/3.1/language/types.html#qubits) motivates explicit reset.
