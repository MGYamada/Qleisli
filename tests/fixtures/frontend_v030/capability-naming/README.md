# Capability and adjoint naming migration

This packet implements the ordinary naming decision in [Issue #45](https://github.com/MGYamada/Qleisli/issues/45), within edition 2026 and release 0.3.0-alpha.
`Applicable`, `Adjointable` and `Controllable` name capabilities. `adjoint(U)` and `controlled(U)` name static descriptions; `adjoint(U)(q)` applies the former.
Old predicates, `inverse_op`, `controlled_op` and constructed `inverse(U)(q)` reject with located migrations. Ordinary single-stage inverse/controlled calls retain name resolution. General isometry adjoints and external providers remain unsupported.

`source-map.json` extends the existing checked fixture selector. Predecessor bytes, manifests, initial sources, independent oracles and earlier validation records remain intact. File copies contain only renamed capability/constructor tokens. The additional small project copies preserve their complete source inventories. The migration helper checks provenance, not meaning or acceptance; its token invariance test is separate from existing independent operator tests.

The corpus packet under `corpus/migrations/capability-naming-v030/` preserves complete selected source projects and semantic faults. Its observations record actual commands before activation. The dirty-tree comparison checks 34 accepted original IR artifacts byte-for-byte against the 9ae55073 compiler and retains the rejected measurement-adjoint case. This is bounded evidence, not a source-preservation theorem.

`inventory-review.json` records the reviewed source identities. The public AST, native acceptance and capability derivation rules are unchanged. The 4,000-case ownership generator, order, seed and both public consumers remain unchanged. Reference rules describe the existing conservative derivations; no new constitutional interpretation or guarantee is admitted. QS, PR and quantitative RS retain their pending broader duties.

`precommit-validation.json` records the shared local check groups and preserves
earlier failures separately. Rust 1.98.1 and MSRV 1.85.0 each passed 977 tests in
102 executables, retaining 52 existing ignored tests and all 4,000 ownership
cases. The final ownership runs took 373.35 and 372.79 seconds, respectively;
these concurrent local timings are observations, not a promised speedup.
Both Clippy/research profiles, source integrity, source contracts, independent
source semantics, fixed mdBook and preflight groups passed. These results bind
the recorded working inputs. Clean-commit native comparisons and the final
same-commit hosted result remain separate requirements. This naming unit does
not complete every acceptance condition of #45.

`clean-native-validation.json` records the six selected shared native groups
on clean commit `2cfe37f29dec2567b6db7d2cb8ad613acd67da34`: pure raw, observation,
small corpus, QPE, arithmetic and QPE clients. All passed in 96.71 seconds,
including host preparation. The other 61 native groups were omitted from this
local selection and remain required by hosted CI. The observation comparison
retains root/dependency evidence and independent exact Kraus semantics. This
subsequent record does not claim that later commits ran those local groups.
