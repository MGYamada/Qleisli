# Installed CLI playground context

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0

The user asked the assistant to play with the installed `qleisli` command.
This is an informed small-system exploration, not a blind authoring benchmark,
source-preservation proof, hardware test or release validation. The assistant
read the repository instructions, README, roadmap, trust boundary, constitution,
authority hierarchy, adopted interpretation/admission records and relevant
existing Bell, Grover, BV, feedback and inline teleportation sources first.
The exact deployed model identifier and sampling settings are unavailable.
No independent authoring model or subagent was used.

The context, first sources and hashes were written before checking these new
projects. The installed CLI does not expose a working `--version` flag; the
project version below is the repository version, not measured CLI provenance.
Binary SHA-256 values identify the observed executables, not their source builds.
An earlier unrecorded-timestamp setup call to `qleisli run examples/bell
--format=json` refused a missing checker. After explicitly selecting the local
checker, the existing Bell example returned 00/11 at approximately 1/2 each.
An earlier 32-shot seed-42 sample also succeeded. These setup calls are not
counted as the timestamped authoring observations in this session.

`check_constitution.py` passed current record/source/evidence identity checks;
no trusted continuity base was supplied, and no fresh full proof replay is
claimed. QS/PR/RS/EXACT retain pending broader proof/enforcement obligations;
the two ordinary QLV1 ownership/scope guarantees keep their recorded premises.
Kernel source-policy checking passed. The selected binary's digest matches the
historical local build digest in current-evidence.json; that is not portable
binary attestation. The compiled declaration audit was also started separately.

## Predictions fixed before execution

- Bell: (|00> + |11>)/sqrt(2), hence P(00)=P(11)=1/2.
- Independent H preparations: four outcomes with probability 1/4 each.
- GHZ: (|000> + |111>)/sqrt(2), hence only 000 and 111 at 1/2.
- H H |0> = |0>; H Z H |0> = |1>. The phase becomes visible after H.
- Corrected teleportation of |->: phase/parity bits uniform and X readout 1,
  hence 001, 011, 101, 111 with probability 1/4 each.
- Deliberately omitting the Z correction leaves X readout equal to not m1:
  001, 011, 100, 110 each at 1/4. It can typecheck while being algorithmically
  wrong relative to the intended teleportation contract.
- Existing two-bit Grover example: marked 11 after one amplification step.
- Existing BV example: recover the fixed hidden string 10.
- Existing feedback example: the first bit is uniform and the second is 0.
- Measuring the same logical owner twice must reject.
- Leaving a quantum owner unused at return must reject.

These are independent small analytical expectations; floating-point comparison
uses absolute tolerance 1e-12 and retains raw probabilities without renormalizing.
Sampling counts are finite observations, not exact probability proofs.
Deliberate counterexamples are outside the repair sequence. No source repairs
are planned; any needed repair must use a complete new numbered attempt.
