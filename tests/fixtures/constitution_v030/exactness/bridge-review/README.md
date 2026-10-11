# Release ledger validation bridge

This small independent regression records a missing binding between the ledger
bytes validated by the constitutional service and the ledger bytes captured by
the release producer/consumer. It does not challenge the admitted mathematical
guarantees or establish release readiness.

`reproduce.py` uses the existing disposable `SyntheticRelease` test fixture.
The constitutional service, version plan, hosted context, successful build
receipts and release acceptance are explicitly simulated. The actual release
checker, Git checks, artifact checks and receipt comparison execute. No Lean
replay, real hosted job, publication or human authority is asserted.

The service returns a digest for distinct ledger bytes containing the exactness
supplement and reports three base obligations plus one supplemental obligation.
The outer captured/final bytes omit the supplement. The unfixed checker accepts
and reports only three pending obligations; the final outer bytes are unchanged.
The fixed checker must reject the mismatched digest before accepting a receipt
or interpreting its proof disclosure.

`before-record.json` and `before.stdout.json` preserve that observation and the
original release checker/test bytes. The source-identity record was captured
after the constitutional checker gained its new digest return field, but before
the release checker consumed it; this timing is explicit in the record. No
historical source/evidence file was rewritten. `after-record.json` and
`after.stdout.json` record rejection by the repaired checker using the identical
driver, captured ledger digest and simulated validated ledger digest. The
constitutional service now returns the digest of its already validated bytes;
both release boundaries compare it against their captured ledger bytes. Missing
digest also rejects. The ordinary unchanged checks and exact receipt-result
comparison remain in place.

The exact saved driver contains the observed workspace path. The recorded run
was `python3 /private/tmp/qleisli-release-ledger-substitution.py` from the
repository root. Running it constructs and cleans up only a small disposable
synthetic repository. It does not run a Rust/Lean build or native checker.
