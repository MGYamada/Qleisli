# Published 0.2.1 review reproductions, repaired/planned in 0.2.2

These are curated minimal sources based on the user-supplied review, saved
before the local checks. They are local fixtures, not another external corpus
source or a controlled model-authoring study. The reviewer's numpy harness,
6000-case result and Rust fuzz were described but not supplied; they are not
claimed as locally executed evidence.

- [TH repeated 512 times](repeat_512/main.qli) records the reported exact-product
  capacity failure. Local 0.2.2 now accepts and runs it; the Rust regression also
  checks 400, 1000 and 1024 repetitions and an explicit 1024-call equivalent.
- [Flat Toffoli return pattern](toffoli_flat/main.qli) records the remaining
  incompatible shape. It still rejects, while changing the pattern and result
  type to the existing nested product works. The [tuple issue](https://github.com/MGYamada/Qleisli/issues/15)
  tracks the v0.3 specification/migration question.

The independently authored [source differential harness](../../../scripts/test_qli_differential.py)
saves each generated source before invoking the CLI. Its fixed-seed gate-word
specification exercises the exact extractor through `apply_contract`; a separate
complex state oracle checks X/Y/Z measurement statistics, coherent phase/control,
classical feedback and reset. Numerical results are regressions, not semantic
evidence or a proof of source translation. Its report records seed, case count,
ordered source hash, compiler hash and harness hash for reproduction.

Executed records for this repair are retained here:

- [Minimal reproduction checks](reproductions.json).
- [Seeded differential checks](differential-validation.json).
- [Small semantic-QFT checks](qft-semantic-validation.json).
- [Full finite corpus checks](corpus-validation.json).
- [Rebuilt Lean registry, theorem types and audits](registry-validation.json).
- [Combined local validation and exclusions](validation.json).

See the review response for dispositions and
the development record for local validation.
Published 0.2.1 artifacts and earlier validation files remain immutable.
