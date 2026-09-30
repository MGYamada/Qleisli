# Terminology and notation

Status: **editorial conventions for the English specification and API contracts**
(updated 2026-09-28). The [language specification](language-spec.md),
[grammar](syntax-v0.md), [module and sealed-API specification](standard-library.md),
the [semantic-contract supplement](semantic-contracts-v0.1.md),
the [function-contract supplement](function-contracts-v0.1.md),
and [ordinary-library contract ledger](stdlib-contracts.md) are authoritative
English documents. Design goals and planning notes now have English editions;
their authority and proposal status are identified in the
[documentation map](documentation-map.md). They do not override current source/API
contracts. Japanese operational guidance, historical milestone records, legacy
anchors, and glossary terms remain supporting material. Translation and notation
cleanup do not change acceptance rules or turn tests into proofs.

The [language evolution framework](language-evolution.md) separates current
normative rules from future design notation and defines the English records
required before selecting an extension. Imaginary algorithm code is design
material, even when it resembles `.qli`; it is not executable source evidence.

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
| desugaring layer | 脱糖層 | A producer outside the independent acceptance boundary that translates convenience syntax/representations into already specified core operations, preserving meaning; see the detailed definition below. |
| coefficient domain | 係数領域・係数環 | The exact scalar representation and its specified arithmetic, equality, conjugation and interpretation. A future domain parameter does not itself establish those laws or enable arbitrary angles. |

## Desugaring layer

**Desugaring** is the meaning-preserving translation of convenient surface
constructs or equivalent representations into **already specified core
operations**, with explicit interfaces, ownership and effects. It introduces
no new primitive meaning or checker acceptance rule. Here “layer” denotes a
responsibility, not a dedicated crate, a particular AST pass or a currently
implemented universal importer.

Its input is a resolved source construct or an adapter's decoded representation;
its output is untrusted core syntax/IR and, where needed, proposed evidence
and source-location mappings. Producers must preserve evaluation order, linear
owners including `Q<Unit>`, exact phase, axis/result order, effects, cleanup
obligations and specified resource limits. Ordinary definitions, static gate
modifiers and bounded syntactic repetition can use this layer when their
translation is defined. Desugaring need not flatten an entire program: a future
specified hierarchy can retain calls/repetition as its existing core nodes.
Existing inverse/control capability premises still apply; desugaring cannot
grant access to an opaque operation merely because it is mathematically unitary.

Parsing, name/type checking, proof search, target selection and optimization
are separate responsibilities, even when implemented in the same frontend.
Source checks remain required; “outside the trusted checker” is not permission
to omit them. Foreign parsing is not itself desugaring. Only the part that maps
already supported foreign meanings to existing core operations qualifies.
An unsupported arbitrary-angle gate cannot become sugar by rounding its angle;
approximate synthesis needs its own [error contract](coefficient-domains.md#exact-approximate-and-device-contracts).

The independent verifier and evidence kernel must check the produced artifact;
the producer cannot issue a checked handle or authorize cleanup. Acceptance
establishes the core artifact's checked properties, not correspondence with the
original input. Preserving source/foreign meaning remains a separate translation
obligation. Rewriting checked IR requires renewed validation and evidence
rebinding/invalidation. A post-verification numerical adapter, such as the
current qif runtime adapter, is not this pre-verification desugaring layer and
does not remove its legacy rules from the trusted checker.

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
in the [conformance record](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/specification-status.md), with the command and scope.
