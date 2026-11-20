# Documentation build environment

Contributors should begin with the [architecture principle](reference/architecture.md)
and [authority hierarchy](reference/authority.md). Major language/tooling designs
must record how they preserve that architecture before implementation.

[Qleisli Programming Language](introduction.md) is the book's
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
python3 scripts/check_book.py
```

Run the commands from the repository root and open `target/mdbook/index.html`.
`mdbook serve docs` provides a local preview. These generated files are already
ignored under `target/`; the Markdown sources are under `docs/src/`.
Missing chapters fail the build instead of being created automatically.
`scripts/check_book.py` reads the rendered book and the sources, as
[Checked rules](#checked-rules) describes.

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
descriptive, and draft notation must stay identified as a draft.

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
compatibility together. Such tools belong to this documentation environment.
Use `qli` fences for Qleisli examples; mdBook's Rust playground is disabled,
and an HTML build does not execute or verify Qleisli programs.

The [v1 algorithm goals](imaginary-v1/index.md) describe planned capabilities
and link to their design issues. Specification chapters derive from adopted
decisions, the code and its proofs. Book links to repository material outside
its chapters use repository URLs so they also work in the rendered HTML.

## Style guide

The Language Reference follows the shape of *The Rust Reference*: each chapter
states the rules of one subject, and a reader can skip how the compiler
implements them. These rules apply to a chapter when a change writes or
rewrites it. A chapter that predates them keeps its wording until its rewrite.
[Diagnostics and recovery](reference/diagnostics.md) is written by these rules,
and [Coherent basis maps](reference/coherent-basis.md) shows the layout of a
chapter on one construct.

Four chapters render adopted constitutional records and are exempt. They keep
the wording that their records bind:
[ratification](design/ratification.md),
[authority hierarchy](reference/authority.md),
[initial interpretations](design/initial-interpretations.md) and
[initial guarantees](design/initial-guarantees.md).

### Voice

- Use the present tense and the active voice. Write "the checker rejects the
  call", not "the call will be rejected".
- Put one idea in each sentence. Split a sentence longer than about 30 words,
  and keep each paragraph to one topic.
- Do not write "now", "new", "currently", "still" or "remains" for the state of
  the implementation. The book describes the language as it is. Git and the
  changelog record how it changed.
- Use "actual", "exact" and "complete" only where the word carries a technical
  meaning, as in "an exact phase".

### Terms

- Define a term before you use it. Set the term in bold where the text defines
  it, and nowhere else.
- Use one word for one concept.
- Write "capability" for Applicable, Adjointable and Controllable, and
  "capability requirement" for an entry of a `requires` clause that names
  one. Write "access" for what a capability permits, as in "inverse access",
  and for the `excl` and `ctrl` markers of a call.

### Rules and their placement

- Begin a chapter with a paragraph that defines its subject.
- Lay out a section on a construct in this order: its syntax, a description,
  its rules as a bulleted list under the label "Rules:", then examples.
- Write a rule with "must", "must not" or "may", and name the diagnostic code
  of a program that breaks it.
- Keep every rule in one place. Other chapters link to that section instead of
  restating the rule.
- Put implementation detail in a quoted block that begins with
  **Implementation note.** Such a note names the component that does the work.
  It adds no rule, so a reader can skip it.
- State a limit as a number.

### What stays out of the body

- Dated update notes, release names, and Issue or pull request numbers belong
  in a final section "History". The body states the result of a decision.
- State the limits of the implementation and the proof status once, in a
  section "Status and limits" near the end of the chapter. Keep the separation
  of code, tests, proof, preservation and specification review there.

### Examples

- Label a block `qli` for Qleisli source, `text` for grammar and output, and
  `sh` for commands.
- Take an example from a source that a test checks, and say whether the checker
  accepts or rejects it.
- In a lesson, ask readers to predict an observable result before they run
  the program. Change one expression at a time so they can explain the
  difference. When teaching from a rejected program, show the diagnostic
  alongside the expression that caused it and let readers try the repair.
- When a later lesson reuses a project, name the file to edit and say
  whether a listing replaces the file or just one expression. Give readers
  an observable result to check before they make the next edit.

### Checked rules

`scripts/check_book.py` enforces the rules below on the chapters that
`SUMMARY.md` lists. The other rules of this guide need a reviewer. Passing the
check is not a review of what a chapter says.

| Rule | Chapters |
| --- | --- |
| No word of the form `<T>` outside a code span, because it renders as an HTML tag | Every chapter |
| Every code fence is closed | Every chapter |
| A code span in a table row writes a pipe as `\|`, because a bare pipe ends the cell | Every chapter |
| No "now", "new", "newly", "currently", "still", "remain", "remains", "remained" or "remaining" in prose | Checked chapters |
| An Issue or pull request reference stands only in a section "History" | Checked chapters |
| A paragraph has at most 120 words. A list item and a quoted block each count as one paragraph; a table row is not counted. | Checked chapters |
| A code fence has the label `qli`, `text`, `sh`, `toml` or `json` | Checked chapters |

The word rule reads prose only. It skips code, link targets and words in
double quotation marks, which mention a word rather than use it.

A checked chapter is a chapter in neither of two lists in the script:

- `EXEMPT` names the four constitutional chapters that keep the wording of
  their records and the v1 goals chapter that links each goal to its design issue.
- `PENDING` names the chapters that predate this guide. Remove a chapter from
  the list in the change that rewrites it. The check fails on a pending chapter
  that keeps the rules, and on a list entry that `SUMMARY.md` does not name.

A chapter that joins `SUMMARY.md` is therefore checked from its first change.
`python3 scripts/test_check_book.py` runs the checker's own tests.

## Maintaining the book

The chapters of the book live directly in `docs/src/`. They are the only
maintained copies. Edit the chapter files directly.
The book builds with mdBook's default preprocessors, without include wrappers
or custom build steps.

The architecture chapters display SVGs rendered from the Mermaid sources in
`docs/src/architecture/diagrams/`. If a diagram changes, regenerate its SVG
with [Mermaid CLI 12.2.0](https://github.com/mermaid-js/mermaid-cli/releases/tag/12.2.0)
from the repository root. The book build copies the rendered files.

```sh
for name in system compiler verifier rust-crates; do
  diagram="docs/src/architecture/diagrams/$name"
  mmdc --no-font-embed --svgId "qleisli-$name" \
    --input "$diagram.mmd" --output "$diagram.svg"
done
```

The [introductory lessons](learn/first-qubit.md) teach with executable
programs. The roadmap identifies planned features explicitly. Repository root documents
are linked where needed, not embedded. Links between chapters are relative;
links to code, fixtures and build configuration use their repository URLs.
No external plugin is required.
