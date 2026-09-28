# Three-source QLI input corpus

**24 finite translations, eight per approved source**, selected for Qleisli
0.1.9 on 2026-09-28. The [adopted policy](POLICY.md) restricts external inputs to
QuantumKatas, Qualtran Bloqs and PennyLane Demos and fixes their license handling.
The [manifest](manifest.json) pins commits, original paths, file hashes, symbols,
mathematical contracts, parameter specializations and exclusions.

The development method is to [start with quantum programs as they ought to be
written](../docs/design-philosophy.md#start-with-the-quantum-programs-we-want-to-write),
then grow a language with AI that can express and check them. These executable
translations expose the gap between current QLI and that goal. They do not adopt
new syntax, prove scalable algorithms, or replace the ideal-source drafts.

## Use and layout

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
| qualtran | [add2](qualtran/add2/README.md) | For a=a0+2*a1 and b=b0+2*b1, map &#124;a,b> to &#124;a,(a+b) mod 4> with amplitude +1 on the whole input space. |
| qualtran | [xor2](qualtran/xor2/README.md) | Map &#124;a,b> to &#124;a,b xor a>, for two-bit registers; phase +1. |
| qualtran | [less_than2](qualtran/less_than2/README.md) | Map &#124;a,b,t> to &#124;a,b,t xor [a<b]>, where a=a0+2*a1 and b=b0+2*b1. |
| qualtran | [qrom2](qualtran/qrom2/README.md) | For address a=a0+2*a1, XOR data[a] into the two-bit target, with data=[1,2,3,0]; retain address and arbitrary target. |
| qualtran | [and_phase](qualtran/and_phase/README.md) | Compute a positive-control AND into a clean auxiliary, phase it by Z and uncompute: diag(1,1,1,-1) on the two inputs. |
| qualtran | [qft2](qualtran/qft2/README.md) | F4[y,x]=exp(2*pi*i*x*y/4)/2 with output reversal included. Integer bit order is first leaf least significant. |
| qualtran | [qpe2](qualtran/qpe2/README.md) | Two-bit coherent QPE with rectangular/uniform window and U=S=T^2. On &#124;00>&#124;b>, report b/4 and retain the target. |
| qualtran | [reflection2](qualtran/reflection2/README.md) | I-2&#124;++><++&#124;, with prepare=H^2 and upstream global_phase=+1. |
| pennylane_demos | [qubit_rotation](pennylane_demos/qubit_rotation/README.md) | Apply RY(pi/2) RX(pi/2) exactly, including scalar phase. From &#124;0>, the Z expectation is zero. |
| pennylane_demos | [teleport](pennylane_demos/teleport/README.md) | The measured teleportation instrument returns ((phase, parity), Bob), each branch weight 1/4, preserving reference correlations. |
| pennylane_demos | [qaoa_vertex_cover](pennylane_demos/qaoa_vertex_cover/README.md) | One layer exp(-i*alpha*sum X) exp(-i*gamma*C) H^4 with alpha=gamma=pi/4; C=3*sum_edges(Zi*Zj+Zi+Zj)-sum_i Zi on edges (0,1),(1,2),(2,0),(2,3). |
| pennylane_demos | [qaoa_maxcut](pennylane_demos/qaoa_maxcut/README.md) | One original gate layer: product RX(2*beta), after product exp(-i*gamma*Zi*Zj/2), after H^4. gamma=pi/2, beta=pi/4; edges (0,1),(0,3),(1,2),(2,3). |
| pennylane_demos | [vqe_excitation](pennylane_demos/vqe_excitation/README.md) | DoubleExcitation(pi): &#124;0011> -> &#124;1100>, &#124;1100> -> -&#124;0011>, all other basis vectors unchanged. The default input is Hartree-Fock &#124;1100>. |
| pennylane_demos | [classifier_layer](pennylane_demos/classifier_layer/README.md) | Rot(0,pi/2,0)=RY(pi/2) on all four wires, followed by the original CNOT ring 0->1->2->3->0. |
| pennylane_demos | [qpe3](pennylane_demos/qpe3/README.md) | Three-bit QPE for PhaseShift(3*pi/4)=T^3, returning low-weight-first phase bits and the retained target. |
| pennylane_demos | [phase_lock](pennylane_demos/phase_lock/README.md) | The first wire is a lock meter. H, controlled FlipSign(0111), H XORs the predicate [key=0111] into that meter and preserves the four-wire key. |

The VQE example is the four-orbital excitation at angle pi, not molecular
energy minimization. QAOA preserves each original four-node graph but fixes
one layer and its angles. PennyLane QPE changes the original 1/5 phase to
3/8 explicitly; it does not claim an approximation of the original circuit.
Qualtran And becomes a compute/phase/uncompute kernel, and the comparator is a
finite checked basis lift rather than a scalable synthesis. Each case records
these boundaries before it can count as a port.

## What was validated

[Recorded local results](validation.json): **24 shipped examples, 9,412 semantic
probes and four rejection cases** passed with the Rust 1.98.1 compiler on macOS.
The report binds the manifest, final QLI files, oracle script and compiler by
SHA-256. It is a reproducibility record, not a signed attestation.

- For each of the 20 unitary kernels, enumerate every computational input and
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
- Derive Z0, the QAOA cost expectation and expected MaxCut edge count on the host
  from the distributions. These are finite numerical aggregations, not a new
  QLI optimizer, gradient API, noisy shot estimator or chemistry calculation.
- [Local negative fixtures](negative/manifest.json) reject duplicate ownership,
  post-measurement reuse, measurement adjoints and dirty auxiliary use. They are
  deliberately authored counterexamples, not failed external source translations.

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
[24-project and rejection smoke tests](../tests/input_corpus.rs). The docs job
checks provenance and the Python harness regressions.

## Authoring evidence and next language work

[Session records](authoring/session.json) preserve complete sources before each
check, hashes and actual JSON diagnostics. The first attempt passed 19/24 cases.
Five failures exposed unsupported Boolean `or`, `let` in basis bodies, and
`repeat_static` inside restricted `with_computed`. Attempt 02 rewrote these with
existing syntax and passed all 24; attempt 03 only removed unused imports and
also passed. These are informed translations with prior repository and upstream
access, not a controlled LLM benchmark. No failed attempts were invented.

The [authoring report](../docs/qli-authoring-feedback.md) and
[backlog](../docs/v0.2.0-backlog.md) retain these gaps, phase-preserving rotation
boilerplate and the boundary around continuous parameters/host optimization.
Preserve the real attempts as language-design evidence instead of treating
these finite adaptations as the final desired notation.
