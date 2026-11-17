# Invisible source character first observation

This informed #245 lexical study uses one Unicode tag scalar in ordinary
documentation prose. The project source and edition manifest were retained
before the first observation. The review base is `a844010f`. The executable
was an existing local beta debug build, recorded by SHA-256 in the
observation. It predates the review base. The scanner and lexer source are
unchanged between the prior phase integration `0bc4c3d2` and the review
base. This record does not attest to the prior executable build tree.

The transcript preserves both output streams, with the invisible scalar
escaped in JSON. The Markdown observation covers the source-only `doc`
command. The executable regression separately checks current behavior.
