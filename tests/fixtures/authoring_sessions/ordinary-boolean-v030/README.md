# Ordinary Boolean first-source observations

Twelve complete small projects, their context, manifests and independent
expectations were fixed before any execution. `first-files.json` binds those
28 original files. Ten projects are desired forms and two are deliberate
staging counterexamples. Nine desired projects also include explicit closed
`observe main()` probes. No first source needed an in-place repair.

The existing parameter-pattern MSRV CLI and native checker are identified in
`identity-before.json`. The CLI digest is
`aa1d49498f9bc7b7e75509680c8cde6d516d074c9aa889dc8b043cdb7216f4fd`.
The recorded prior implementation/stdlib hashes matched the inspected source
before this study, and were unchanged afterward. This is reused build evidence,
not a fresh build of the current Git HEAD. No production source, GitHub Issue,
other session or session index was edited. No Cargo/Lean build or source/binary
snapshot copy was performed.

`observe.py` recorded 33 actual calls, preserving exact argument vectors,
stdout/stderr, exit status, timestamps and source/executable identities:

| First-source family | Finite check | Sized check | Separate closed probe |
| --- | --- | --- | --- |
| Constants | Pass | Literal expression unsupported | `01` |
| `not`/`xor`/`and` | Pass | Boolean expression unsupported | `010` for input `10` |
| Ordinary product copy/drop | Pass | Closed wrapper's literal unsupported | `00` for input `01` |
| Ordinary/quantum mixed passthrough | Pass | Boolean expression unsupported | `10`/`11`, each about 1/2 |
| Classical control | Pass | Runtime branch unsupported | `11` |
| Measured feedback | Pass | Runtime branch unsupported | `00`/`11`, each about 1/2 |
| Measured Boolean results | Pass | Boolean expression unsupported | `001`/`110`, each about 1/2 |
| Unit helper retaining observation | Pass | Observe result must currently be one Bits value | `1` |
| Eager `0 and measure_z(q)` | Pass | Boolean expression unsupported | `0` |
| Explicit static branch producing Bit | Nat profile unsupported | Literal expression unsupported | No wrapper |
| Static Nat used as runtime Bit | Nat profile unsupported | Unbound/consumed runtime value | No wrapper |
| Runtime Bit used as static Nat | Register profile unsupported | Unknown natural name | No wrapper |

The simulator's unrounded probabilities are retained in the JSON records.
These probe values agree with the corresponding independent expectations;
they do not establish the complete open-function truth table or arbitrary
reference behavior. In particular, probability zero from the eager-AND probe
alone cannot establish that the RHS measurement was retained. The later
implementation tests must inspect the actual accepted operations/source events
as well as compare the independently specified instrument action.

The sized checker prepares **every declaration**. Selecting `main::f` does not
skip its sibling closed wrapper. The copy/drop source therefore stops at its
wrapper's literal before reaching the classical-entry lowering boundary; this
observation is not evidence that the library copy/drop judgment itself failed.
Earlier dedicated library studies and current API tests separately cover that
distinction. The Unit helper probe similarly stops at the selected root's
result-profile restriction, before any claim about omitted readout outcomes.

There is no current CLI classical-input assignment option. `--basis` concerns
quantum axes and was not used as a substitute. A closed wrapper evaluates fixed
ordinary arguments; it does not supply or validate a new open-classical API.
Prospective native tests must bind the actual artifact and compare the
conditional channel, e.g. `K_c = <c| tensor X^c` for measured feedback, on two
quantum bits with reference dimension two. Ignored measurement labels require
summing unnormalized branch density matrices; comparing output probabilities
or coherently summing amplitudes is insufficient.

This packet is preparatory evidence under the existing plan. It does not adopt
a new contract, discharge a guarantee, implement dynamic branches, prove source
preservation, or validate a release. All quantum examples use at most two bits.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
