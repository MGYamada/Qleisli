# Nine small translations for 0.2.9

Three additions per approved frozen source, with one to three data qubits.
Upstream commits, files and source-specific notices are unchanged.
The [session](session.json) preserves complete first sources before checking.
These are informed translations, not controlled model benchmarks.
No upstream framework or maximum-size experiment is run.

Contracts cover the full minus-state extension, signed phase, uniform preparation,
three-bit borrow, a zero predicate, a nonzero-label reflection, signed rotations
and path/edge QAOA sublayers.

All nine [first checks](check-initial.json) passed; zero positive-source repairs.
The [semantic validation](semantic-validation.json) covers 646 full-entry
probes for these cases and detects all nine type-correct faults. The complete
[87-case run](../../validation-v0.2.9.json) passed 15,889 probes, four source
rejections and 63 faults. X/Y interference retains absolute phase and input/output
ordering; tolerance 1e-11 is numerical validation, not a general proof.

The first proposed minus-state fault used Z H, which is exactly H X. The
[calibration record](fault-calibration.json) retains that real failed negative
check and its original source. The corrected fault H X Z agrees on zero input
but changes the second column; the oracle detects it. No positive source was
changed to fit the reference and no compiler behavior was altered.
