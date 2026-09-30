# Canonical reshape metadata and encoding

The [pre-check packet](packet.md) and [contract](../../../docs/size-expressions.md)
bound this experiment. The desired source and original parse error are in the
[authoring session](../authoring_sessions/reshape-v021/session.json).
`reshape::<...>` remains a draft, with no repaired executable source yet.

`Reshape-first.lean.txt` preserves the unchanged first compiling source.
[first-build.json](first-build.json) records that the attempted pre-build copy
had a wrong relative path; the identical source was copied immediately after
its successful first compilation. This is not a before-check snapshot claim.
The later source adds explicit finite-basis inverse/composition laws and u32
port limits from the existing hierarchy profile.

The first compiled-declaration audit rejected a generated partial helper,
`QleisliKernel.Reshape.width._unsafe_rec`, even though source compilation and
native tests succeeded. [The actual diagnostic](compiled-audit-first.json)
and [pre-repair source](Reshape-before-compiled-audit.lean.txt) are retained.
Using the standard `List.foldr` for width/encoding removes project recursive
helpers; the final complete compiled audit passed after this change. The initial
source never issued production evidence.

[native-validation.json](native-validation.json) records **118 cases: 89
accepted metadata requests and 29 rejections**, with **1,050 basis probes** and
**3,150 phase-sensitive reference coefficients**. The independently implemented
Python oracle parses recursive trees and combines child labels by their widths;
Lean traverses prefix atoms. Native encoding, canonical index transport and its
inverse agree, with no dense matrix. Larger valid widths up to 16 use selected
labels; finite probe counts are not a substitute for the general Lean theorem.

The negative cases retain changed typed atoms, erased Bits(0), equal-type axis
swaps, duplicate/new wires, reused/out-of-range owners, malformed/deep trees,
wrong independent endpoints and exact budget boundaries. Unit-only positive
cases still have one input and one output owner. The API has no arbitrary body,
phase or owner-list field; it cannot certify a phase-mutated circuit or drop a
second zero-width owner. Such emitted bodies/frames require the future source
producer's independently checked structural expansion.

`native-before-index-map.json` preserves the first encoding comparison.
`native-before-audit-repair.json` retains the native result before replacing
generated recursion. The final report binds source/harness/native binary hashes
and actual build/execution output. Run it with:

```sh
python3 scripts/test_lean_reshape.py --record tests/fixtures/reshape/native-validation.json
```

The script is part of kernel CI. This is internal adapter metadata validation;
external semantic evidence remains false, all component schemas stay disabled,
and production Rust acceptance is unchanged.

[validation.json](validation.json) records the final build/audit, reduction and
regression scope, including the temporary stale-registry test result and its
successful rerun. [registry-validation.json](registry-validation.json) binds
both audited Lean packages and fresh checker replay to the current source
revision, keeping all external schema entries disabled.
