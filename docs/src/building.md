# Documentation build environment

[The Qleisli Programming Language](introduction.md) is the new book's
starting point. [book.toml](https://github.com/MGYamada/Qleisli/blob/main/docs/book.toml) configures its source, metadata and HTML
output; [src/SUMMARY.md](https://github.com/MGYamada/Qleisli/blob/main/docs/src/SUMMARY.md) defines the chapter order.

## Pinned mdBook

The authoritative tool pin is `MDBOOK_VERSION: '0.5.4'` in the `check-docs` job
of [the CI workflow](https://github.com/MGYamada/Qleisli/blob/main/.github/workflows/ci.yml). CI downloads the corresponding
official Linux binary, verifies its pinned SHA-256 and checks `mdbook --version`
before building. The HTML is retained as a CI artifact for review.

For a local source installation, run:

```sh
cargo install mdbook --locked --version 0.5.4
test "$(mdbook --version)" = "mdbook v0.5.4"
mdbook build docs
```

Run the build from the repository root and open `target/mdbook/index.html`.
`mdbook serve docs` provides a local preview. These generated files are already
ignored under `target/`; the Markdown sources remain under `docs/src/`.
Missing chapters fail the build instead of being created automatically.

The source installation uses mdBook's own Rust requirements. A matching
[official binary](https://github.com/rust-lang/mdBook/releases/tag/v0.5.4)
is an alternative; neither choice changes Qleisli's Rust MSRV or dependencies.
The upstream [Rust Book](https://github.com/rust-lang/book#requirements)
documents the same exact-version, locked source-installation pattern.

When updating mdBook, review its release notes, update the CI version and
official binary checksum together, update the local commands here, then inspect
the rendered book. This tool pin is separate from product-version maintenance.

## Source authority and tool responsibilities

**mdBook renders the specification; it does not participate in the specification.**

Normative authority belongs to adopted source documents and decisions. A
`CONSTITUTION.md` or Language Reference must state its adopted status and scope;
neither is established by adding it to the book. Tutorial chapters are
descriptive, and draft notation must remain identified as a draft.

mdBook is an external documentation CLI. It is not a Qargo dependency, part of
the Qleisli toolchain, or something for `qleisliup` to manage. Its configuration
controls presentation and book assembly, not language acceptance, qrate
resolution or API introspection.

Qleisli-aware API documentation belongs to `qlidoc`. The current implementation
offers `qleisli doc` for source documentation; this setup does not introduce a
standalone `qlidoc` command. API extraction and semantic checks stay with the
Qleisli ecosystem. mdBook may render their resulting documentation as content.

No external mdBook plugins are enabled. If a preprocessor or renderer such as
KaTeX or a link checker is added, pin its version and installation alongside
mdBook in the documentation CI, record the local setup here, and review their
compatibility together. Such tools remain in this documentation environment.
Use `qli` fences for Qleisli examples; mdBook's Rust playground is disabled,
and an HTML build does not execute or verify Qleisli programs.

The retained [imaginary-v1 drafts](imaginary-v1/index.md) and
[Lean backend plan](lean-backend-plan-v0.3.md) are embedded in the book with their
existing status. New chapters derive from adopted decisions, current code and
proofs. Book links to repository material outside its chapters use repository
URLs so they also work in the rendered HTML.

## Maintaining the book

The existing build guide, backend plan, imaginary-v1 index and requirements
now live directly in `docs/src/`. These chapters are the only maintained copies;
their former locations have been removed. Edit the chapter files directly.
The book builds with mdBook's default preprocessors, without include wrappers
or custom build steps.

The retained planning prose is documentation debt while a coherent tutorial is
written. Its draft or planned status remains explicit. Repository root documents
are linked where needed, not embedded. Links between chapters are relative;
links to code, fixtures and build configuration use their repository URLs.
No external plugin is required.
