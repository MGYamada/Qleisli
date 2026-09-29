# Typed layout implementation record

This informed CD-3 exercise is not a controlled model benchmark or an extra
external corpus source. See the [component contract](../../../docs/lean-layout-slice.md).

The untouched [first source](first_source/main.qli) was saved before checking.
It already passes the Rust source checker: three owners, including `Q<Unit>`,
move into a flat three-field result without implicit tuple reassociation. The
[baseline](baseline.json) records that source check and the then-unsupported
Lean `--layout` invocation. The source's accepted Rust behavior is retained. Both primary and MSRV CI jobs
check this source directly, and both installed local builds passed it again.

The [proposed artifact](reorder.qhl) and [independent request](reorder.qhr) were
also saved before that invocation. The owner permutation is `[2,0,1]`; the
axis permutation `[1,2,0]` is different because the first owner has no wires.
Dropping it must reject even when every physical axis is still present.

[Layout-first.lean.txt](Layout-first.lean.txt) is the first checker/proof attempt,
retained before compilation. [Actual Lean diagnostics](first-lean-diagnostics.txt)
show that `at` was a reserved token. The implementation renamed it `indexAt`
and supplied the explicit accepted-permutation proof to the final rewrite.
[Reduction-test diagnostics](first-reduction-diagnostics.txt) exposed missing
`DecidableEq` for an `Except` result; those closed equalities now use kernel
reduction by `rfl`, not native proof evaluation. The first
[native test diagnostics](first-native-diagnostics.txt) found a test mutation
that accidentally left an output port unchanged; the repaired case selects
another owner's axis, retaining the rejection obligation.

The final [native suite](../../../scripts/test_lean_layout.py) runs 230 fresh
process decisions, including independent small basis/amplitude oracles, a
reference coordinate, Unit/Bits0 ownership, altered inverse maps and metadata,
well-typed wrong swaps and strict transport/capacity tests. Its 16-axis cases
do not enumerate basis states; checker dense dimension remains zero.
[After-state observations](after.json) preserve actual commands, diagnostics,
metrics and hashes. [The isolated rebuild](clean-build-record.json) records
exact build/audit/replay results with no copied `.lake` and no external packages.

The concrete obligation removed is manual assurance that owner and axis maps
agree with full type trees. There are no new `.qli` constructs or standard APIs,
no source-to-layout producer and no reduced number of author-written source
adapters in this packet. Checking work is charged independently of the number
of basis states; no controlled authoring or timing comparison was measured.
Full hierarchy integration, arbitrary encodings, QFT/QPE schema proofs and
production acceptance remain open.
