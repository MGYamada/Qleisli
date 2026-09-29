# Fourier host first attempts and counterexamples

The [packet](../fourier-host-packet.md) binds the existing shared QFT source/IR
producer to an independent named request through the fresh host path.

- [Composite checker](FourierRoot.lean.txt) and [compiler output](compile.txt)
  used the wrong namespace for `Failure`; it belongs to the artifact namespace.
- [Mathematical composition](HierarchicalFourierRoot.lean.txt) compiled as saved;
  [its diagnostic file](math-compile.txt) is empty. The existing unitary and
  coefficient proofs refer to the same actual denotation by uniqueness.
- [Protocol](Protocol.lean.txt), [Main](Main.lean.txt) and
  [protocol diagnostics](protocol-compile.txt) preserve the initially missing
  explicit import of the new checker. A later named-boundary proof also needed
  removal of unused simp arguments under warnings-as-errors.
- [Rust host](hierarchical.rs.txt), [request producer](request.rs.txt),
  [integration test](qft_hierarchy.rs.txt) and [native fixture generator](test_hierarchical_fourier_host.py.txt)
  were saved before their initial checks. The [first native result](../fourier-host-native-first.json)
  and [diagnostics](native-diagnostics.txt) show a faulty counterexample that
  removed reachable SWAP nodes and failed whole-artifact reachability first.
  Replacing those SWAP actions with identity, in both implementation and meaning,
  preserves typing and reachability while violating the requested Fourier map.
- [Reindex diagnostics](reindex-diagnostics.json) exposed aliased Python fixture
  dictionaries: renumbering definitions also mutated meaning references. A JSON
  round trip separates the tables before testing independent numbering.
- [Boundary counterexample](boundary-counterexample.json) and
  [diagnostics](boundary-counterexample.txt) demonstrate a real omission in the
  initial, unreleased composite path. Legal explicit Bit/Bits adapters preserved
  Fourier coefficients but allowed a named `qft` request with a Bit boundary.
  The published meaning requires one closed Bits register. The pure composite
  checker now enforces that existing rule with `namedBoundary`; tests retain
  both the Bit adapter and an open output-owner example. This does not restrict
  the reusable coordinate inspector or change supported released behavior.
  The concrete [Bit artifact](named-bit-boundary.json)/[request](named-bit-boundary-request.json)
  and [open-boundary artifact](named-open-boundary.json)/[request](named-open-boundary-request.json)
  were reconstructed after discovery from the same retained generator and saved
  here for review; they are not represented as pre-check snapshots.

[Pre-boundary audit](pre-boundary-registry.json), [runtime checks](pre-boundary-runtime.json)
and [host checks](pre-boundary-native.json) are historical intermediate results,
not validation of the corrected acceptance path. Consult the current
[native record](../fourier-host-native.json), [registry audit](../fourier-host-registry.json)
and [runtime validation](../fourier-host-runtime-validation.json) for that result.
No failed or stale-binary run is counted as final validation.

Copyright 2026 Masahiko G. Yamada. Apache-2.0.
