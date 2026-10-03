# Final publication rehearsal follow-up

Full CI run 37141484534 passed all 67 native comparison groups and the Rust
production suite, then exposed two remaining distribution failures: the Linux
foreign/Python harness inherited no checker selection, and the retained research
adapter still called the removed Rust verifier. The raw logs and successful
bounded local replacement checks are recorded in `validation.json`.

The harness now selects its requested checker for both environment and per-call
routes. The research adapter obtains fresh native acceptance before extracting
its independent symbolic comparison graph. Its term/proof rules are unchanged.
No production Rust/Lean definitions changed, and no proof gate is declared closed.
A subsequent exact-commit full CI run is required before publication.
