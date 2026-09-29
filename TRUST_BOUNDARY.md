# Trust boundary

Fixed architectural policy, adopted 2026-09-29. This partition is to remain
unchanged as Qleisli develops. [Proof status and execution assumptions](docs/lean-kernel-migration.md)
remain explicit; this policy does not declare the planned proofs complete.

1. **Trusted:** Lean's proof kernel; the correspondence between the declared
   gate set and physical hardware under its stated assumptions; and `std`'s
   mathematical specifications as the intended meanings. Library implementations
   must still satisfy those specifications through ordinary verification.
2. **To prove:** the [Qleisli Soundness Theorem](docs/release-milestones.md#qleisli-soundness-theorem-v050),
   connecting accepted IR to its requested meaning, and the
   [Physical Realizability Theorem](docs/release-milestones.md#physical-realizability-theorem-v1),
   connecting that meaning to the actual synthesized gate implementation.
3. **Untrusted; reject unless independently validated:** frontend output,
   including proposed IR and evidence. Human or LLM authorship confers no
   authority; failed validation cannot be bypassed.
