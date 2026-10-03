# 0.2.3 review response in development 0.2.4

The supplied review covers a released artifact. The following changes apply to
unpublished 0.2.4; published tags/packages and earlier validation reports remain
immutable. The reviewer's Rust/Lean results are external observations, not checks
claimed as rerun here. This is an informed implementation/repair exercise, not
a controlled model evaluation or a general proof.

| Review finding | Response and remaining scope |
| --- | --- |
| Missing S/S†/T†/identity/scalar source actions | [Issue 130](https://github.com/MGYamada/Qleisli/issues/130): sealed `s`, `sdg`, `tdg`, `id`, `phase_eighth`; existing T gates and zero-axis monomial IR only. Exact phase, type trees, linear Unit ownership and no scalar auxiliary wire are tested. |
| Corpus idioms | Ten active kernels and bundled QFT source use the aliases. Two private QFT wrappers are removed, with all twelve public library functions unchanged. New complete attempts precede actual checks; original attempts and the frozen six VM-22 comparison projects stay intact. Historical snapshots still contain old idioms and are not current authoring advice. |
| OpenQASM rejects semantic IR, including Bell | The existing terminal profile is retained. [Issue 132](https://github.com/MGYamada/Qleisli/issues/132) defines a v0.4.0 untrusted LiftBasis synthesis experiment with independent actual-table/clean-workspace checking. General compute/control/contract decomposition is still pending; no all-example export claim. |
| Realizability requires workspace | [Issue 120](https://github.com/MGYamada/Qleisli/issues/120) and the [theorem contract](../../../docs/release-milestones.md#synthesis-workspace-contract) distinguish semantic unitarity from target realizability. Require `C E0 = E0 U`, retained phase/references, explicit target workspace and total live resource bounds. Clean existence does not imply dirty-workspace preservation. |
| QFT/QPE-specific acceptance and parallel pipelines | [Issue 131](https://github.com/MGYamada/Qleisli/issues/131) specifies the 0.3/0.4 review and migration gates. Generic contracts need independently proved library meanings and complete actual-definition/binding coverage. `PathSum.compile_sound` alone is not a full complex Fourier theorem or a complete equivalence normalizer. Mathlib-free acceptance and Mathlib proof packages retain distinct duties. |
| Scattered capacities | Existing [Issue 94](https://github.com/MGYamada/Qleisli/issues/94) tracks typed producer/acceptance/transport/execution groups. Different budgets are not forced equal; capacities and toolchains are preserved in this PATCH. Budgets are not quantitative Resource Safety evidence. |
| Branch wire identity | The [finite specification](https://github.com/MGYamada/Qleisli/blob/v0.2.7/docs/language-spec.md) explicitly distinguishes fresh phi logical IDs from physical allocation/layout; even unchanged merged frames are renamed. [Issue 126](https://github.com/MGYamada/Qleisli/issues/126) tracks target correspondence. |
| Pair/Tuple shape | Existing Rust-aligned exact shape rules remain; [Issues 15](https://github.com/MGYamada/Qleisli/issues/15)/[27](https://github.com/MGYamada/Qleisli/issues/27) carry the 0.3 type/migration review. No implicit axis flattening is adopted. |
| Numerical zero residues | [Issue 133](https://github.com/MGYamada/Qleisli/issues/133) requires a separate display/exactness contract. Current raw numerical outcomes stay intact; no blanket threshold erases genuine small probabilities or issues evidence. |
| Quick reference / qargo | Quick reference now says 0.2.4 and its new complete alias example has a checked output oracle. The qargo gap is the separately linked 0.2.1 loader, already recorded; a schema-compatible std manifest alone does not complete namespace loading ([53](https://github.com/MGYamada/Qleisli/issues/53), [107](https://github.com/MGYamada/Qleisli/issues/107)). |
| Iterative RawOp Drop / clone cost | Existing bounded rejection/drop protection is retained; no public move-out change in PATCH. |

## Exact counterexamples and evidence

[c3x.qli](c3x.qli) retains the supplied small four-bit odd permutation.
[Exact Rust regressions](../../static_semantics.rs) confirm its table swaps
14/15 and accepts as a semantic unitary; independently check every QFT3 entry
against positive F8 and compute determinant `i` without floating arithmetic.
These regressions are not realization certificates or Lean proofs. Primary
existence/obstruction references are [Giles–Selinger](https://arxiv.org/abs/1212.0506)
and [Shende et al.](https://arxiv.org/abs/quant-ph/0207001).

[Corpus replay](corpus-validation.json) passes 48 cases, 12,893 independent
complex-entry/protocol probes, four source rejections and 24 type-correct
semantic faults. It includes global phase through controlled X/Y interference;
no upstream framework or new maximum-size case is executed. The ten modernized
kernels remove six constant-one scalar flags, four private identity wrappers
and repeated T spellings. Two historical active comparison projects retain
scalar/identity idioms to preserve the frozen VM-22 source identity. A versioned
migration of that comparison boundary remains separate.

[Validation record](validation.json) binds actual commands, results and source
hashes. Corpus session `review-checks.json` and `review-semantics.json` append
real observations beside preserved complete revised sources. Lean executable
code is unchanged by this review packet; no new Lean build/proof result is
claimed here. Earlier VM-24 checks remain in their own fixtures. Production
Rust authority, disabled external schemas and S05/PR/RS proof gates remain.
