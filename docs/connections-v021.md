# 0.2.1 bounded Python, OpenQASM 3 and QIR connections

Status: **implemented and locally validated on 2026-09-30; selected for 0.2.1**.
See the [release record](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/releases/v0.2.1.md) for publication status; the Python
wheel's registry distribution is separate from the Rust crate. This additive host layer
uses the existing Rust finite verifier. It adds no `.qli` form, quantum primitive,
proof authority or production hierarchical acceptance rule. Heavy shared-QPE
integration and proofs now belong to [0.2.2](v0.2.2-plan.md).

## Interfaces

`qleisli interop ACTION INPUT --input=FORMAT` returns one version-1
`qleisli.result` JSON envelope. ACTION is `check`, `run`, `sample`, `emit-ir`,
`emit-qasm` or `emit-qir`. FORMAT is `qasm`, `qirf` or `qli`. INPUT is a file,
`-` for standard input (qasm/qirf only), or a source project directory (qli).
`sample` requires `--shots=N --seed=S` with the existing CLI bounds, SplitMix64
sequence and fresh state per shot. An optional `--format=json` is accepted;
this subcommand always emits JSON. Usage exits 2, other failures 1, success 0.
Exports return `result.text`; they do not write a destination file. Source
loading uses the existing bounded policy. QASM is limited to 1 MiB, QIRF to
the existing 16 MiB transport limit, before full input allocation.

Python package `qleisli` exposes `Client`, `Program` and `QleisliError`.
`Client.from_openqasm`, `from_qir`, `from_ir` and `compile_project` return a
program carrying QIRF bytes. Its `check`, `run`, `sample`, `to_openqasm` and
`to_qir` methods invoke the Rust boundary anew. A Python object or mutated
artifact never bypasses verification. Rust diagnostics are retained, including
source spans or artifact pointers when supplied. Configure the installed
`qleisli` executable explicitly or through PATH; a source-built executable is
supported without pretending it is a bundled native wheel.

### Structured diagnostics

Artifact import/export failures preserve the original JSON pointer in
`related`, using the same `json_pointer: /…` entry as `verify-ir`. Available
OpenQASM input spans appear in `primary` with original UTF-8 byte offsets and
one-based line/Unicode-column coordinates, treating CRLF as one newline.
File-backed input uses its filename; standard input uses `-`. Python retains
the diagnostic array. Usage, I/O and unlocated errors keep `primary: null`;
exports do not invent source spans. These compatible 0.2.2 repairs are covered
by [#56](https://github.com/MGYamada/Qleisli/issues/56).

## QIR input profile

Use the [M1.1-A terminal profile](interop-m1.1.md), exact twelve-gate vocabulary,
QIR specification revision and QIR 2.0 output convention. The optional reader
uses **PyQIR 0.12.5** (MIT; the tested wheel bundles LLVM 20.1) to parse text or bitcode
and verify LLVM. No hand-written LLVM parser and no imported code execution.
Python 3.11+ is the host baseline. QIR parsing is optional; default Rust builds
remain free of LLVM/Python dependencies. Unsupported wheel platforms must use
QASM/QIRF or a separately supported reader environment.

Accept one closed zero-input entry, static resource counts at most twelve,
one acyclic unconditional block chain (named, unnamed or mixed blocks), direct calls to the specified QIS/runtime
symbols, terminal Z measurements and one ordered result array. Validate all
declarations and signatures, module/profile flags, measurement attributes,
pointer IDs, initialization placement, measurement/result uniqueness and output
ordering. Reject extra definitions, dynamic resources, unknown calls, loops,
unvisited blocks, conditional branches, custom QIS bodies, post-measurement
gates, reused measured wires/results and unsupported output structures. Module
assembly, mutable globals and unrecognized semantic attributes are unsupported.
Parsing is capped at 1 MiB, with bounded functions, blocks and instructions.
CFG traversal uses actual LLVM identity; block display names are not identities
([#55](https://github.com/MGYamada/Qleisli/issues/55)).

The reader translates only the validated terminal slice to canonical QASM with
explicit initial reset and output order; Rust reconstructs logical ownership
and independently verifies the resulting IR. Unrecorded measured systems and
other terminal wires are explicitly discarded. LLVM validity, profile checks,
Qleisli IR validity and general translation correctness are distinct: these
adapters do not supply a formal correspondence theorem or an algorithm proof.
Adaptive circuits and general Python-framework object adapters remain later work.

## Validation and packaging

Require independently authored LLVM/QASM fixtures, output-order and phase
interference checks, invalid profile/signature/CFG/resource tests, text/bitcode
equivalence, Rust/Python error equivalence and fresh seeded sampling. Run the
reference OpenQASM parser and standard LLVM verification independently of the
reader, using small circuits. Package the Python host layer as a wheel, test
installation in an isolated environment and state its external Rust-executable
requirement. All-in-one platform wheels remain a separate distribution gate.
No registry publication or device execution is implied.

Primary references: [PyQIR APIs](https://www.qir-alliance.org/pyqir/api/pyqir.html),
[pinned PyQIR release](https://pypi.org/project/pyqir/0.12.5/), and the
[pinned QIR Base Profile](https://github.com/qir-alliance/qir-spec/blob/f5647346542d5a65225c3eb349847fe4df01d1b2/specification/profiles/Base_Profile.md).

The [local validation record](../tests/fixtures/interop/connections-validation.json)
records macOS arm64/Python 3.14.5, the installed wheel and tested inputs. PyQIR
publishes CPython abi3 wheels for macOS arm64/x86-64, Windows x86-64 and Linux
x86-64/aarch64 with its declared OS/glibc minima; their presence is not a claim
that this change was tested on all those platforms. CI adds Ubuntu 24.04/Python
3.12 and LLVM 18 checks; the local independent LLVM run used 22.1.6.
