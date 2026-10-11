# QLI authoring corpus

The programs are checked-in `.qli` source, not Rust-generated source strings.
[qli_corpus.rs](../../qli_corpus.rs) copies the relevant example modules to
a temporary project, installs each client as `main.qli`, and checks its complete
distribution. Run `cargo test --test qli_corpus`.

| Directory | Role |
| --- | --- |
| `protocols` | Clients of [protocol components](../../../examples/protocols/README.md): seven input states, retained reference, inline/modular equivalence, dense coding, swapping. |
| `algorithms` | Clients of [operation algorithms](../../../examples/operation_algorithms/README.md): phase grid, X eigenstates, off-grid and correlated inputs, four marks, overshoot, signed overlap. |
| `accepted` | Self-contained cleanup evidence, pair contracts and product reassociation, plus n-ary tuple and basis-pattern cases. Two preserved predicate sources use explicit current translations, as described below. |
| `rejected` | Self-contained minimal reproductions: unsupported syntax/interfaces and useful ownership/access rejections. Expected structured categories are in the Rust harness. |
| `faults` | **Intentionally incorrect**, type-correct replacement modules. The harness installs them as `teleportation.qli` or `estimation.qli` and checks the specific wrong distribution. Do not copy these as working examples. |

Every source file must belong to an exercised case; the inventory test rejects
unregistered files. Rejection tests pin categories. The dedicated
[ergonomics suite](../ergonomics/README.md) checks precise binding locations
and the new pattern/tuple forms. When a language limitation is addressed, migrate its
fixture to accepted tests with an explicit contract and update the
authoring report. The corpus is
an authoring/semantic regression suite, not a measured LLM pass-rate benchmark.

The original `accepted/pair_contract.qli` and
`accepted/basis_tuple_pattern.qli` retain their historical multi-parameter
predicates. Under the 0.3.0 explicit predicate-domain rule, the harness first
checks their `arity` rejection, then executes the separately stored unary
translations and checks the original complete distributions. The
[translation map](../frontend_v030/predicate-domain/current-translations.json)
binds both source hashes and their test cases; the original files are not
silently rewritten or skipped.
