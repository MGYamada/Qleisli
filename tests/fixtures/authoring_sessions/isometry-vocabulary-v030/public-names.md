# Public Rust names and effect diagnostics

After the first spelling stage in commit `7571cc96`, the current Rust variants
`ir::Effect::Iso`, `frontend::ast::FnKind::Iso` and
`frontend::lexer::TokenKind::Iso` are renamed to `Isometry`. Callers update
variant references; no Rust compatibility constant or variant is introduced.
The enum positions, effect ordering, body inference and assertion rule are
unchanged. Diagnostics produced from these variants use `Isometry` too.

`after-public-names/observing-assertion.json` records the unchanged original
counterexample with the updated actual diagnostic. Earlier diagnostics retain
their original bytes, including the old public name. The unsupported external
unitarity explanation remains a semantic error without a tracker link.

The QIRF 1/2 codec explicitly maps `Effect::Isometry` to the existing `"iso"`
wire tag. The checked source graph and native hierarchy adapter likewise keep
their existing tags. The Lean Raw, QftGraph and hierarchical artifact effect
constructors still use `iso`; their formal/transport migration remains a
separate inventory and continuity question under #57. No Lean representation,
checker, proof or protected guarantee changes in this Rust naming stage.
Legacy source-prefix retirement and remaining active-source migration are
still required; this record does not close #57 or admit a new guarantee.
