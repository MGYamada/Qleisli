# Independent bounded expectations

These expectations follow the [posted contract](contract.md). They are review
oracles for the next implementation, not new execution results. Generic source
checking, concrete preparation, artifact acceptance and amplitude observations
must be reported separately.

## Ten immutable original cases

| Original project | Required source/preparation outcome | Independent semantic or rejection reason |
| --- | --- | --- |
| `private-forward-sibling` | Generic checking succeeds; public `main::f` can instantiate and call private `helper` declared later. Direct host selection of the private helper rejects. | `f` and `helper` both act as the one-qubit identity. An unqualified sibling call has the current module's privilege; a host entry has none. |
| `public-sibling-provider` | Generic checking succeeds. Instantiate `main::f` with `U=main::gate`; the public sibling `main::gate` is also a legal host entry. | Both entries implement the one-qubit identity. The provider receives its own `DefId`, not the entry's AST position. |
| `same-name-separate-modules` | Generic checking succeeds; instantiate the same root separately with `U=a::gate` and `U=b::gate`. | Both original providers implement identity, while their source declaration identities and private helper references remain distinct. These identical bodies alone do not detect a provider swap; use the distinct-meaning extension below. |
| `import-terminal-bindings` | Generic checking and `main::f` preparation succeed. Imports bind `flip` and `phase` by terminal names in the private wrapper. | Both imported bodies are identity, despite their names. Their composition is identity; the oracle must not infer X or phase behavior from spelling. |
| `unused-bad-function` | Generic checking rejects the unused sibling before any entry can prepare. | `unused` returns the empty classical tuple and leaves its quantum input live. Source checking cannot ignore it merely because `f` does not call it. The old finite profile's empty-tuple rejection is a different historical observation. |
| `mutual-siblings` | Reject a mutual declaration cycle. | `f -> g -> f` is not structurally decreasing self-recursion of one identical definition. |
| `duplicate-siblings` | Reject the second `f` at its source location. | Two declarations in one module cannot share a terminal name. Do not keep only one projected function. |
| `private-imported-sibling` | Reject `dep::helper` at the import location. | A same-module private sibling is accessible inside `dep`; the external `main` module has no such privilege. |
| `import-rename-still-unsupported` | Preserve the parse rejection at `as`. | This unit adds no import-alias grammar. |
| `import-collides-sibling` | Reject the conflicting import at its source location. | Imported `dep::gate` cannot replace the local `main::gate`. |

The four successful semantic oracles are `I_2`: for an arbitrary one-qubit
input and arbitrary untouched reference amplitudes `psi[a,e]`, the result is
exactly `psi[a,e]`. Validation should check both basis columns and a correlated
reference probe. A successful source parse alone does not establish this oracle.

## Additional bounded checks before completion

- Reverse declaration order in an acyclic sibling pair and select a public
  sibling whose source position differs from its name-sorted `DefId` position.
  Clone and move the parsed collection before instantiation. Both entries must
  still select their own body, signature and lexical table.
- Give `a::gate` the one-qubit X meaning and `b::gate` the one-qubit S meaning,
  using the existing `x` and `phase[1,2]` primitives. Independently expect
  `X|a> = |1-a>` and `S|a> = i^a |a>`. Instantiate both providers within one
  parsed collection and through different entries, so caches cannot conflate
  identical terminal names. Check complex coefficients, including relative
  phase on a superposition or correlated reference; do not compare only output
  probabilities.
- Compare an equivalent split-module and sibling implementation that applies X
  to the first input owner `q` and S to the second input owner `r`. In labelled
  coordinates, independently require
  `|a>_q |b>_r -> i^b |1-a>_q |b>_r`, so the coefficient from `(a,b)` to `(c,d)`
  is `i^b * delta(c,1-a) * delta(d,b)`. Lift this equation by identity on an
  untouched reference. This two-qubit oracle detects owner-axis interchange and
  dropped phase. Use the repository's documented axis encoding only when
  translating the labelled coordinates into the simulator vector. The two
  source/artifact identities differ; equal proposal bytes are not required.
- Reject an unused sibling with an ill-typed result, an invalid static branch,
  or an ownership-invalid zero-iteration fold body. Do not rely on entry
  reachability or a particular concrete specialization to skip generic checks.
- Reject a sibling cycle through a static operation provider even if the
  provider is under `repeat_op(0, ...)` or otherwise unused by concrete code.
  Keep decreasing natural self-recursion only when the resolved callee has the
  identical `DefId`. Reject nondecreasing self-recursion and distinguish calls
  to an unrelated same-named declaration in another module.
- Preserve current empty-module and unsupported declaration/type/effect
  rejections. Preserve existing single-function diagnostics and unchanged
  single-function proposal bytes/native outcomes in the lexical fixture.

These new checks use at most two active qubits plus a small untouched reference.
No maximum-size cases, new capacity, alias syntax, general mutual recursion,
source-preservation theorem or broader guarantee are introduced.
