# Initial call expansion and proof attempt

The two `.lean.txt` sources were saved before their first compilations.
`compile.txt` records the first producer-proof failure: a case split had
already rewritten the lookup goal, so the proof needed `rfl` at that position.

The mathematical proof's first compilation reported an uninferred interface,
the wrong orientation for an equivalence rewrite, a matrix-law simplification
failure and an ambiguous `sequence` name. Repairs supplied exact interfaces,
used a directed permutation-sum lemma and qualified the existing operator laws.
No axiom, `sorry`, native proof shortcut or increased proof limits were used.

The first native suite expected an eight-bit call with nine separate owners
to pass; the existing aggregate checker returned `limit`. This distinct
fragmented-header case is now retained as `nine-owner-capacity`. The sized
register cases use `Bit`, `Bits<n-1>` and an explicit empty Unit owner, covering
widths 1–8 and a separate `Bits<0>` boundary. This does not resolve the measured
fragmented-header capacity issue or claim that every 16-wire artifact fits.
