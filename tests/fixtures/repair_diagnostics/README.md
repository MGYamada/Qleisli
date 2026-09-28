# Repair-oriented diagnostic cases

Run `cargo test --test repair_diagnostics`. Each file is a separate rejected
source project. Tests check expected/actual types at ordinary and basis calls,
returns, static providers/composition, branches, primitives and conditions.
Binary association and Unit nodes must remain visible in printed types.

The suite also uses the existing rejected/accepted cleanup pair and
`false_cleanup`: suggesting a logical contract must not authorize an incorrect
one. Text and JSON output retain rejection, source locations and categories.
Only explanatory messages change; no error schema or acceptance rule changes.
