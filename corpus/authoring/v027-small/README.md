# Nine small finite translations for 0.2.7

Three additions per approved frozen source, with one to three data qubits.
[Manifest](../../manifest.json) records symbols, fixed inputs, contracts and
exclusions; upstream commits, hashes and licenses are unchanged.

[Session](session.json) preserves complete first sources before checking.
Eight of nine first checks passed; controlled H used an invalid four-argument
qif spelling. The actual [diagnostic](check-initial.json) is retained; the
complete second snapshot uses the documented branch syntax and all nine
[checks](check-repaired.json) pass. These are informed translations with prior
source/oracle access, not a controlled model benchmark.

[Semantic validation](semantic-validation.json) checks every complex entry
with X/Y interference: 798 probes and nine paired type-correct faults. Cases
cover coherent controlled H, selected-bit entanglement, even-label axis order,
modular overflow/carry, strict comparison with arbitrary target, constant XOR,
half-turn scalar phases and noncommuting QAOA cost/mixer order. Tolerance 1e-11
does not issue exact evidence or prove general source preservation. No upstream
framework or new maximum-sized experiment was run.
