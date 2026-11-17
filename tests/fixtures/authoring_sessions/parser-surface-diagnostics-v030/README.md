# Parser surface diagnostics

This informed authoring session for [#237](https://github.com/MGYamada/Qleisli/issues/237)
preserves four invented statement spellings and three malformed quantum
headers. The first sources copy the shapes in the issue. The existing
development CLI from the #245 scanner worktree produced the seven recorded
parse failures. The common parser in that worktree matched
`a844010fcfb4db023f60da02350d21c672c96366` when the observations were
recorded. The scanner changes reject additional Unicode format characters.
Each source here uses ASCII. The recorded SHA-256 identifies the binary
that actually ran. No build attestation ties the binary to a particular
tree.

The native checker path intentionally points to a missing file. Each
observation ends at the parser and records the original output and JSON
location. The live Rust regressions read these sources and check the
guidance and byte spans. The historical commands remain inert.
