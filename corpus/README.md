# Three-source QLI input corpus

The [shared sized experiments](sized/README.md) now compile and independently
inspect Xor, GHZ and QFT source at all selected widths. QFT includes an imported
adjoint client and shared calls. They reuse existing pinned
inputs and have a separate development execution path. The 42 finite CLI cases
below use the production frontend. The bounded `qleisli sized` source/CLI slice
and measured QPE are recorded in the
[current checkpoint](../tests/fixtures/authoring_sessions/measured-qpe-v021/checkpoint.md);
general correspondence and full-profile migration remain open.
The [coherent QPE continuation](sized/qualtran_qpe/README.md) now passes its
small selected configurations with static operation providers and full-state
diagnostics. Further maximum-size checks are deferred by the 2026-09-30 user
decision. Initialization, readout and `CBits` now have a separately checked
bounded measured-source slice; accepted sizes and remaining gates are explicit
in that checkpoint.
The [shared AddK/Equals continuation](sized/qualtran_arithmetic/README.md) now
passes widths 0–3, using coherent recursive controls and shared XOR/complement
to restore input registers. Its independent arithmetic oracles cover all small
basis inputs and reference columns, including incorrect carry and restoration.
These experiments do not add to the finite production CLI translation count.
The [local order/amplitude integration clients](../tests/fixtures/sized_clients/README.md)
now reuse the same coherent QPE at small sizes, with explicit operation
forwarding and independent phase/reference formulas. They are local verification
material under the existing policy, not a fourth external corpus. Their
measured clients now have bounded source/CLI integration; general correspondence
and wider production integration remain open.

**42 finite translations, fourteen per approved source**, including six
1–3-qubit additions for 0.2.3 and six simple
1–3-qubit additions for 0.2.2 on 2026-09-30 and six additions for 0.2.1 on
2026-09-29. The original 24-case intake was selected for 0.1.9
on 2026-09-28. The [adopted policy](POLICY.md) restricts external inputs to
QuantumKatas, Qualtran Bloqs and PennyLane Demos and fixes their license handling.
The [manifest](manifest.json) pins commits, original paths, file hashes, symbols,
mathematical contracts, parameter specializations and exclusions.

The development method is to [start with quantum programs as they ought to be
written](../docs/design-philosophy.md#start-with-the-quantum-programs-we-want-to-write),
then grow a language with AI that can express and check them. These executable
translations expose the gap between current QLI and that goal. They do not adopt
new syntax, prove scalable algorithms, or replace the ideal-source drafts.

The 2026-09-29 [tuple migration](../docs/tuple-shapes.md) spells former binary
trees explicitly in `qualtran/less_than2`, `pennylane_demos/vqe_excitation` and
`pennylane_demos/phase_lock`. [Attempt 04](authoring/session.json) preserves the
new source snapshot and real before/after checks; the
[exhaustive after-state](authoring/tuple-shapes-semantic.json) passes all 9,412
semantic probes. Earlier attempts, upstream pins, numerical contracts and
source-specific attribution remain intact.

The [0.2.1 expansion session](authoring/v021-expansion/session.json) preserves
the six new first attempts separately. Existing commits stay pinned. Two more
PennyLane demo files and their author metadata were reviewed at that same
commit; their repository-wide Apache-2.0 terms apply and neither file declares
an exception. No imported library implementation, image, dataset or model is
copied. Original 24-case snapshots and validation reports remain unchanged.

The [0.2.2 simple session](authoring/v022-simple/session.json) adds SWAP and
Fredkin, constant XOR and bitwise complement, and exact RX/phase kickback.
It reuses only frozen files at the existing commits; upstream hashes, license
reviews and author notices remain intact. All six first checks passed without
source repair. One-bit phase kickback explicitly narrows the original four-bit
key; RX fixes the original two rotation parameters to `(pi/2,0)`. These are
small finite translations, not completion of the shared-QPE integration goal.

## Use and layout

The [0.2.3 small-system session](authoring/v023-small/README.md) adds odd-parity
preparation and a signed Bell singlet, constant comparison/equality, exact RY
and one Ising ZZ edge. It reuses the same frozen commits/files and reviewed
licenses. All six first checks passed; 490 full-entry semantic probes pass and
six type-correct faults are detected, including errors invisible to zero-input
probabilities. The enclosing [Qargo.toml](Qargo.toml) selects edition `2026` for
translations, first attempts and faults. This tree is not yet a qrate;
future qrate management does not alter source-specific licensing.

Each case is an independent source project. `kernel.qli` is the reusable
translation; `main.qli` supplies a runnable example; its README states the
contract and limits. Run one case directory, not the entire `corpus/` root.

```sh
cargo build --bin qleisli
cargo run --bin qleisli -- run corpus/quantum_katas/teleport
cargo run --bin qleisli -- run corpus/pennylane_demos/qaoa_maxcut
python3 scripts/check_input_corpus.py
python3 scripts/check_input_corpus.py target/debug/qleisli --exhaustive
```

The metadata-only command checks the closed source list, permission records,
attribution, hashes and authoring snapshots without network access. The last
command checks all finite unitary matrix entries and protocol instruments.
Without `--exhaustive`, execution uses all computational inputs plus selected
interference entries; it is a smaller regression run, not the full matrix check.
A single case can be selected with `--case qualtran/add2`.

Original Q#/Python files under `upstream/` are frozen, unmodified reference
material. They are not QLI inputs and are never executed by the harness.
Only source, metadata, licenses and upstream readmes/notices were copied; no
images, datasets or imported dependencies were brought into the corpus.

## Intake and licensing

| Source | Fixed commit | Treatment |
| --- | --- | --- |
| [QuantumKatas](https://github.com/microsoft/QuantumKatas/tree/1a4740ff70ceffebde73d1434b2dedbe27643300) | `1a4740ff70ceffebde73d1434b2dedbe27643300` | Archived Q# source and translations: MIT, preserving Microsoft attribution. This does not silently track modern QDK exercises. |
| [Qualtran](https://github.com/quantumlib/Qualtran/tree/8db02b8b3fb39d69d2900dcc7b52d9d6a36834c3) | `8db02b8b3fb39d69d2900dcc7b52d9d6a36834c3` | Bloq files and translations: Apache-2.0, preserving Google notices. |
| [PennyLane Demos](https://github.com/PennyLaneAI/demos/tree/3a04df83a16af3a2f0fd9398c0b5cc2c060ebedd) | `3a04df83a16af3a2f0fd9398c0b5cc2c060ebedd` | Demo files and translations: Apache-2.0, with author metadata retained. Former `PennyLaneAI/qml` redirects here. |

The [NOTICE](NOTICE), per-source license files and [policy](POLICY.md) are part
of distribution. Qleisli's own code and original harness remain Apache-2.0;
this mixed intake does **not** make the project `Apache-2.0 OR MIT`.
No selected source file declared a different license. PennyLane's separately
licensed `custom_directives.py` and external assets are excluded. Adding or
replacing a corpus source requires an explicit user-approved policy amendment.

## Examples

| Source | Case | Finite translation scope |
| --- | --- | --- |
| quantum_katas | [global_phase](quantum_katas/global_phase/README.md) | Apply -I to an arbitrary input, including when controlled. XZXZ = -I exactly. |
| quantum_katas | [ghz3](quantum_katas/ghz3/README.md) | Apply CNOT(0,2) CNOT(0,1) H(0); &#124;000> becomes (&#124;000>+&#124;111>)/sqrt(2). |
| quantum_katas | [measure_plus](quantum_katas/measure_plus/README.md) | Return 1 for &#124;+> and 0 for &#124;->. For any input rho, P(1)=(1+Tr(X rho))/2. |
| quantum_katas | [teleport](quantum_katas/teleport/README.md) | Consume the message and Alice half; return ((phase, parity), corrected Bob). Each branch has weight 1/4 and preserves the input density operator and any reference correlations. |
| quantum_katas | [dense_coding](quantum_katas/dense_coding/README.md) | Encode classical (phase, parity) into one Bell half, then decode exactly to the same two bits. |
| quantum_katas | [bernstein_vazirani](quantum_katas/bernstein_vazirani/README.md) | For the fixed hidden string (1,1), H^2 diag((-1)^(a xor b)) H^2 sends &#124;00> to &#124;11>. |
| quantum_katas | [grover2](quantum_katas/grover2/README.md) | One Grover iteration with one marked item 11: D O H^2, D=2&#124;++><++&#124;-I, O=diag(1,1,1,-1). &#124;00> maps to &#124;11> with phase +1. |
| quantum_katas | [qpe3](quantum_katas/qpe3/README.md) | Three-bit coherent QPE for U=T. On &#124;000>&#124;b>, the phase bits encode b/8, first bit least significant; the target survives. |
| quantum_katas | [deutsch_jozsa3](quantum_katas/deutsch_jozsa3/README.md) | Three-bit balanced majority phase oracle between Hadamard layers; preserves the complete unitary and its signed Fourier spectrum. |
| quantum_katas | [bell_measure](quantum_katas/bell_measure/README.md) | Destructive Bell measurement, returning phase/parity in upstream integer order and preserving the conditional state of arbitrary references. |
| qualtran | [add2](qualtran/add2/README.md) | For a=a0+2*a1 and b=b0+2*b1, map &#124;a,b> to &#124;a,(a+b) mod 4> with amplitude +1 on the whole input space. |
| qualtran | [xor2](qualtran/xor2/README.md) | Map &#124;a,b> to &#124;a,b xor a>, for two-bit registers; phase +1. |
| qualtran | [less_than2](qualtran/less_than2/README.md) | Map &#124;a,b,t> to &#124;a,b,t xor [a<b]>, where a=a0+2*a1 and b=b0+2*b1. |
| qualtran | [qrom2](qualtran/qrom2/README.md) | For address a=a0+2*a1, XOR data[a] into the two-bit target, with data=[1,2,3,0]; retain address and arbitrary target. |
| qualtran | [and_phase](qualtran/and_phase/README.md) | Compute a positive-control AND into a clean auxiliary, phase it by Z and uncompute: diag(1,1,1,-1) on the two inputs. |
| qualtran | [qft2](qualtran/qft2/README.md) | F4[y,x]=exp(2*pi*i*x*y/4)/2 with output reversal included. Integer bit order is first leaf least significant. |
| qualtran | [qpe2](qualtran/qpe2/README.md) | Two-bit coherent QPE with rectangular/uniform window and U=S=T^2. On &#124;00>&#124;b>, report b/4 and retain the target. |
| qualtran | [reflection2](qualtran/reflection2/README.md) | I-2&#124;++><++&#124;, with prepare=H^2 and upstream global_phase=+1. |
| qualtran | [add_constant3](qualtran/add_constant3/README.md) | Add 3 modulo 8 with an explicit carry circuit; includes overflow and phase +1 on every input. |
| qualtran | [equals2](qualtran/equals2/README.md) | XOR two-register equality into either target value, restoring both two-bit registers coherently. |
| pennylane_demos | [qubit_rotation](pennylane_demos/qubit_rotation/README.md) | Apply RY(pi/2) RX(pi/2) exactly, including scalar phase. From &#124;0>, the Z expectation is zero. |
| pennylane_demos | [teleport](pennylane_demos/teleport/README.md) | The measured teleportation instrument returns ((phase, parity), Bob), each branch weight 1/4, preserving reference correlations. |
| pennylane_demos | [qaoa_vertex_cover](pennylane_demos/qaoa_vertex_cover/README.md) | One layer exp(-i*alpha*sum X) exp(-i*gamma*C) H^4 with alpha=gamma=pi/4; C=3*sum_edges(Zi*Zj+Zi+Zj)-sum_i Zi on edges (0,1),(1,2),(2,0),(2,3). |
| pennylane_demos | [qaoa_maxcut](pennylane_demos/qaoa_maxcut/README.md) | One original gate layer: product RX(2*beta), after product exp(-i*gamma*Zi*Zj/2), after H^4. gamma=pi/2, beta=pi/4; edges (0,1),(0,3),(1,2),(2,3). |
| pennylane_demos | [vqe_excitation](pennylane_demos/vqe_excitation/README.md) | DoubleExcitation(pi): &#124;0011> -> &#124;1100>, &#124;1100> -> -&#124;0011>, all other basis vectors unchanged. The default input is Hartree-Fock &#124;1100>. |
| pennylane_demos | [classifier_layer](pennylane_demos/classifier_layer/README.md) | Rot(0,pi/2,0)=RY(pi/2) on all four wires, followed by the original CNOT ring 0->1->2->3->0. |
| pennylane_demos | [qpe3](pennylane_demos/qpe3/README.md) | Three-bit QPE for PhaseShift(3*pi/4)=T^3, returning low-weight-first phase bits and the retained target. |
| pennylane_demos | [phase_lock](pennylane_demos/phase_lock/README.md) | The first wire is a lock meter. H, controlled FlipSign(0111), H XORs the predicate [key=0111] into that meter and preserves the four-wire key. |
| pennylane_demos | [lcu_projector](pennylane_demos/lcu_projector/README.md) | PREP–SELECT–PREP† with an explicit H completion; zero-selector block (I+Z)/2. Both quantum owners are returned. |
| pennylane_demos | [kernel_overlap2](pennylane_demos/kernel_overlap2/README.md) | Two-feature RX embedding followed by the adjoint embedding; exact phase and all-zero overlap probability 1/4. |
| quantum_katas | [swap2](quantum_katas/swap2/README.md) | Three-CNOT SWAP on arbitrary two-qubit inputs, with scalar +1. |
| quantum_katas | [fredkin3](quantum_katas/fredkin3/README.md) | Coherently swap two targets iff the retained control is 1; scalar +1 on all inputs. |
| qualtran | [xor_constant2](qualtran/xor_constant2/README.md) | XOR constant 1 into a two-bit register, changing only its low bit. |
| qualtran | [bitwise_not2](qualtran/bitwise_not2/README.md) | Complement both register bits, mapping x to 3-x modulo 4 with scalar +1. |
| pennylane_demos | [rx_quarter](pennylane_demos/rx_quarter/README.md) | RX(pi/2)=(I-iX)/sqrt(2), preserving the scalar required under coherent control. |
| pennylane_demos | [phase_kickback1](pennylane_demos/phase_kickback1/README.md) | A one-bit secret 1 XORs the retained key into the meter through H/controlled-Z/H. |
| quantum_katas | [odd_parity3](quantum_katas/odd_parity3/README.md) | Uniform odd-parity preparation on three wires, retaining all signed input columns. |
| quantum_katas | [bell_singlet2](quantum_katas/bell_singlet2/README.md) | Index-3 Bell preparation with the upstream Z-then-X sign and wire order. |
| qualtran | [less_than_constant2](qualtran/less_than_constant2/README.md) | XOR [x<3] into an arbitrary target, retaining the two-bit input. |
| qualtran | [equals_constant2](qualtran/equals_constant2/README.md) | XOR [x=1] into an arbitrary target and restore mixed-polarity controls. |
| pennylane_demos | [ry_quarter](pennylane_demos/ry_quarter/README.md) | RY(pi/2) with its signed second column; params=(0,pi/2). |
| pennylane_demos | [ising_zz_quarter2](pennylane_demos/ising_zz_quarter2/README.md) | One U_C edge exp(-i*pi*Z0*Z1/4), including absolute scalar phase. |

The VQE example is the four-orbital excitation at angle pi, not molecular
energy minimization. QAOA preserves each original four-node graph but fixes
one layer and its angles. PennyLane QPE changes the original 1/5 phase to
3/8 explicitly; it does not claim an approximation of the original circuit.
Qualtran And becomes a compute/phase/uncompute kernel, and the comparator is a
finite checked basis lift rather than a scalable synthesis. Each case records
these boundaries before it can count as a port.

## What was validated

[Current 0.2.3 results](validation-v0.2.3.json): **42 shipped examples, 12,629
semantic probes and four rejection cases** pass. All **eighteen type-correct
semantic faults** are detected. New translations use at most three data qubits;
the full run retains existing small finite cases and never generates new
maximum-size cases. Source/manifest, oracle and binary hashes bind the report.

[Historical 0.2.2 results](validation-v0.2.2.json): **36 shipped examples, 12,139
semantic probes and four rejection cases** pass with the local 0.2.2 binary.
All **twelve type-correct semantic faults** are detected. The
[six new cases](authoring/v022-simple/semantic-validation.json) account for
290 semantic probes covering every complex entry and six detected faults. No upstream files or
prior reports are overwritten; all added kernels use only 1–3 qubits.

[Historical 0.2.1 results](validation-v0.2.1.json): **30 shipped examples, 11,849
semantic probes and four rejection cases** passed with Rust 1.98.1 on macOS.
All **six type-correct semantic faults** were detected by the independent
oracle after successful source checking. The report additionally pins the
fault manifest and source hashes. These results are finite numerical checks,
not a general proof or upstream-framework execution.

[Original local results](validation.json): **24 shipped examples, 9,412 semantic
probes and four rejection cases** passed with the Rust 1.98.1 compiler on macOS.
The report binds the manifest, final QLI files, oracle script and compiler by
SHA-256. It is a reproducibility record, not a signed attestation.

- For each of the 37 current unitary kernels, enumerate every computational input and
  compare its output distribution with an independent mathematical reference.
  Then measure every complex matrix entry using controlled X/Y interference.
  The reference branch maps the input basis vector to the selected output row;
  the other branch applies the kernel. Their interference distinguishes real
  and imaginary entries, including scalar phase and wire order. This is a
  complete finite matrix comparison within numerical tolerance, not merely
  agreement on computational probabilities or an inverse round trip.
- For both teleportation translations, retain both message bits and perform all
  nine Pauli measurement pairs on a Bell reference and the receiver. Compare each
  classical branch with the ideal identity-channel Choi state. Also run the
  shipped T-phase input example. For `measure_plus`, check six states and the
  upstream Boolean polarity; dense coding checks all four messages.
- Bell measurement adds all four known Bell labels and nine Pauli pairs on the
  two retained references of its Choi input, comparing every classical branch.
- The LCU test compares its full chosen unitary completion. The zero-selector
  block is checked separately against the rank-one projector. Input data 1
  produces selector 1: unpreparing does not imply clean auxiliary return.
- Derive Z0, the QAOA cost expectation and expected MaxCut edge count on the host
  from the distributions. These are finite numerical aggregations, not a new
  QLI optimizer, gradient API, noisy shot estimator or chemistry calculation.
- [Local negative fixtures](negative/manifest.json) reject duplicate ownership,
  post-measurement reuse, measurement adjoints and dirty auxiliary use. They are
  deliberately authored counterexamples, not failed external source translations.
- Eighteen [type-correct semantic faults](semantic_faults/README.md) must pass source
  checking and then fail the mathematical oracle. They test majority/parity,
  Bell-label order, carry, equality, LCU unpreparation and erased rotation phase.
  The six 0.2.2 faults additionally test incomplete SWAP, unconditional Fredkin,
  constant-XOR bit order, partial complement, missing RX scalar and a wrong
  phase-kickback secret. A compiler or harness failure cannot count as detection.

References use elementary complex arithmetic and mathematical equations in
[the runner](../scripts/check_input_corpus.py), without calling QLI or upstream
frameworks to generate expected states. Comparison tolerance is `1e-11`, all
reported outcomes are compared, and normalization is checked. This tolerance
never issues exact evidence or replaces auxiliary zero-return checking.
The QLI frontend and independent IR verifier still check every probe.

No Q#, Qualtran or PennyLane runtime was installed or executed. Thus these are
finite tests against independently transcribed source contracts, not a live
cross-framework differential run or a formal translation-correctness proof.
Upstream decomposition/T-count and QLI resource overhead were not compared;
replacing a general Bloq with a finite basis map does not inherit its complexity.

The primary Rust CI job runs the exhaustive runner; both Rust jobs run the
[30-project and rejection smoke tests](../tests/input_corpus.rs). The docs job
checks provenance and the Python harness regressions.

## Authoring evidence and next language work

[Session records](authoring/session.json) preserve complete sources before each
check, hashes and actual JSON diagnostics. The first attempt passed 19/24 cases.
Five failures exposed unsupported Boolean `or`, `let` in basis bodies, and
`repeat_static` inside restricted `with_computed`. Attempt 02 rewrote these with
existing syntax and passed all 24; attempt 03 only removed unused imports and
also passed. These are informed translations with prior repository and upstream
access, not a controlled LLM benchmark. No failed attempts were invented.

The six 0.2.1 additions all passed their first source checks with **zero source
repairs**, using known syntax and existing rotation workarounds. The historical
24-case observations are checked against their own snapshots; the second
session covers the six additions. Their latest snapshots together must cover
every current source, so growth cannot silently omit authoring records.

The [authoring report](../docs/qli-authoring-feedback.md) and
[backlog](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/v0.2.0-backlog.md) retain these gaps, phase-preserving rotation
boilerplate and the boundary around continuous parameters/host optimization.
Preserve the real attempts as language-design evidence instead of treating
these finite adaptations as the final desired notation.
