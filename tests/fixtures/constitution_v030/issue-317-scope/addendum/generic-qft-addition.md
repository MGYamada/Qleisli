## Canonical generic operation vs fixed-size specializations

The transform namespace must distinguish the **semantic generic operation** from useful fixed-size specializations.

For QFT, the canonical stdlib identity is:

```text
std::transform::qft<N>
```

Fixed-size forms such as:

```text
std::transform::qft2
std::transform::qft3
std::transform::qft4
```

may remain when they are useful as small explicit circuits, pedagogical examples, optimized specializations, regression fixtures, or convenient aliases.

However, they must be semantically subordinate to the generic family:

```text
qft2  ≃ qft<2>
qft3  ≃ qft<3>
qft4  ≃ qft<4>
```

and must not define the ontology of the API.

The project rule is:

> **When a mathematical operation forms a genuine parameterized family, the generic family is the canonical stdlib API; fixed-size names are optional specializations of that family.**

This is deliberately different from the rejected fixed-instance arithmetic APIs above. A hard-coded `qft2` is acceptable because it is a recognizable specialization of a well-defined generic semantic family `qft<N>`. An arbitrary `add2` or `mul2_mod15` is not sufficient to define the future meaning of `std::arithmetic`.

Accordingly:

- documentation should teach `qft<N>` as the primary operation;
- coding agents should prefer `qft<N>` unless a fixed specialization is explicitly useful;
- resource analysis and semantic contracts should be stated for the generic family where possible;
- specialized forms must agree with the generic family at the corresponding parameter;
- implementation specialization must not fork the mathematical meaning.

Add to the 0.3.0 acceptance criteria:

- [ ] Make `std::transform::qft<N>` the canonical semantic QFT API.
- [ ] Treat `qft2`, `qft3`, `qft4`, and analogous fixed-size forms only as optional specializations/aliases/examples of `qft<N>`.
- [ ] Verify each retained fixed-size QFT specialization is semantically equivalent to the corresponding generic instance.
- [ ] Document the general rule that parameterized mathematical families own the canonical API name; fixed-size names do not.
