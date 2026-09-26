# Terminology and notation

Status: **editorial conventions for the English specification and API contracts**
(2026-09-26). The [language specification](language-spec.md),
[grammar](syntax-v0.md), [module and sealed-API specification](standard-library.md),
and [ordinary-library contract ledger](stdlib-contracts.md) are authoritative
English documents. Japanese design goals, planning notes, and milestone records
are supporting material; they do not override those contracts. Translation and
notation cleanup do not change acceptance rules or turn tests into proofs.

| English term | Japanese supporting term | Meaning in this repository |
| --- | --- | --- |
| algorithm | アルゴリズム | A procedure with its own success assumptions and correctness obligations. Older uses of 算法 mean the same thing. |
| frame | frame | Resources outside the currently evaluated expression or callee, including pending arguments; they may be entangled with active resources. Keep this spelling in Japanese notes as well. |
| basis value | 基底値・基底添字 | A value in the separate finite basis language. It is not a measured `CBit` or a quantum ownership handle. |
| classical value | 古典値 | An ordinary copyable value of `Unit`, `CBit`, or a finite binary product of classical types. |
| quantum ownership | 量子所有権 | The linear right to operate on a logical subsystem, including zero-wire `Q<Unit>`; it does not assert state separation. |
| ordinary definition / function | 通常の定義・通常関数 | A `.qli` definition checked through the same source and IR checks as user code. |
| sealed operation | 封印された組み込み操作 | An operation with a compiler-recognized name and specified primitive meaning. It is not an ordinary library definition. |
| protected scope | 保護領域 | The restricted `with_computed` source scope or the specified protected regions in raw `ComputeUseUncompute` IR. State which one is meant. |
| general borrowing | 一般の借用 | A future source feature, such as borrow signatures or arbitrary borrowed work registers. v0 has no general borrowing syntax. Rust's borrow checker is a separate implementation mechanism. |
| pure | 純粋 | Abbreviation for `Unitary` or `Iso`; not an additional member of the source effect order. |
| verified IR | 検査済みIR | IR accepted by the implemented independent verifier. This is not a claim that the verifier or the entire compiler has been formally proved correct. |

Write kets as `|x⟩`, bras as `⟨x|`, inner products as `⟨x|y⟩`, and outer
products as `|x⟩⟨y|`. Use U+27E8/U+27E9 for angle brackets and ASCII `|` for
the vertical bar. Escape vertical bars inside Markdown table cells. Mathematical
code blocks may also use `ket(x)` and `bra(x)` when this makes tensor formulas
easier to read. Source-code operators, generic-type delimiters, URLs, and exact
file excerpts retain their actual syntax.

Keep **proposed**, **specified**, **implemented**, **tested on finite cases**,
**proved on paper**, and **machine checked** distinct. Record the target model,
assumptions, and remaining implementation correspondence whenever citing a proof.
Historical test totals identify their milestone; current validation totals belong
in the [conformance record](specification-status.md), with the command and scope.
