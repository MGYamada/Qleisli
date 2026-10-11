# Sized lexical identity integration

This bounded validation accompanies the common lexical-resolution unit in #32.
The sized profile projects the shared source AST into an owned table of common
`BinderId`/`UseSiteId` references. Generic natural/type checking and concrete
elaboration use those identities. Public host-binding maps and emitted source
steps keep their existing names and shapes.

The first projection still performs the existing per-module profile check before
global name resolution. The second invocation of that same projection attaches
IDs; it neither parses the source again nor adds a second profile-checking rule.
Only numeric IDs and an immutable `Arc<Table>` survive the temporary borrowed
index. Public `ParsedProgram`, `Instantiation` and `ElaboratedProgram` retain
`Send + Sync`. The derived `Debug` representation of `ParsedProgram` and values
retaining it can expose the new private metadata; Debug-text compatibility is
not claimed.

The three added regressions in [sized_source.rs](../../../sized_source.rs)
preserve their exact bounded `.qli` source strings and check:

- Cloning/moving the parsed AST to another thread before instantiation and two
  one-qubit fold activations. The same lexical binder has distinct dynamic
  owner/value identities in successive executions.
- Separate caller, callee and provider declarations all named `n`/`U`, with
  explicit substitution of caller values into the callee's binder IDs. The
  instantiated two-qubit identity retains the public named bindings.
- Profile rejection before later-module parsing or import resolution, including
  the existing one-function-per-module restriction.

[validation.json](validation.json) records the actual command, environment,
toolchain, kernel hash, all Rust source input hashes, test input, registry input
and output hashes. The Rust/input inventory was unchanged across execution.
The saved command passed **37 tests**, including the three new regressions;
**three existing native integration tests were ignored** by this invocation.
Earlier development runs included an environment-only failure when the required
`QLEISLI_KERNEL` variable was absent; the recorded run uses its absolute path.

The complementary [common lexical fixture](../lexical-resolution/README.md)
preserves initial studies and baseline/final observations, proposals, native
checks and one-qubit executions. Its comparison and toolchain records are
separate from this focused test run. These bounded tests are implementation
evidence, not a theorem of source preservation or a new admitted guarantee.
