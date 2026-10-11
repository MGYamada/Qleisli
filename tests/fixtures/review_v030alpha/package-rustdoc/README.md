# Strict API documentation regression

The shared internal type module at commit `6daea68` used unquoted `Q<Bit>`
in a Rust documentation comment. Hosted run `37203327934`, distribution job
`111439463322`, failed its strict package rustdoc step. The local reproduction
records the same invalid HTML tag diagnostic and exit 101.

Marking the type spellings as code fixes the documentation without changing
Rust semantics or public APIs. The same local command then exits 0. The
command, source hash and original stdout/stderr are retained in `before.json`
and `after.json` and their adjacent output files. These observations do not
claim that the complete distribution gate or hosted CI passed.

An isolated copy of commit `6daea68` with only that comment correction also
packages successfully and builds strict rustdoc from the extracted `.crate`.
Its three doctests pass with the required matching native checker selected.
The first doctest attempt omitted that environment selection and failed; its
original output is retained along with the successful unchanged-source retry.
`package-validation.json` records the archive and crate identities and all
four commands. This is bounded package documentation validation, not the
complete distribution gate.
