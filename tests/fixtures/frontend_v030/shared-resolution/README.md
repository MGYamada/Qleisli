# Shared declaration resolution checkpoint

This is an informed, bounded compatibility study for the implementation unit
recorded in Issues #41, #65 and #32 before implementation. It is not a blind
authoring benchmark, a new source feature, or a source-preservation theorem.

The baseline is commit `6daea68fe7efb75df0b627f2d20bd7b409f0cfd3`.
[study.json](study.json) records context and the additional small sources before
their first replay. [initial-study/session.json](initial-study/session.json)
preserves the original ten observations, sources and hashes unchanged. Its
absolute paths describe the original scratch experiment. The initial observer
used a nonexistent underscored kernel filename for one source check; that failed
observation and the successful retry with the actual `qleisli-kernel` are both
retained. No source was repaired in that retry.

[replay.py](replay.py) builds a selected tree and runs fixed commands. It does
not execute instructions from saved records. The baseline can be reconstructed
with `git archive` of the baseline commit's Cargo files, `src`, `stdlib`,
`examples` and `lean-kernel/lean-toolchain`, then built offline using already
available dependencies. Run the driver separately for that tree and the current
tree, with an absolute, freshly built compatible kernel path:

```text
python3 tests/fixtures/frontend_v030/shared-resolution/replay.py \
  --tree /absolute/source/tree \
  --kernel /absolute/path/to/qleisli-kernel \
  --output-dir /absolute/output/directory
```

[before/commands.json](before/commands.json) and
[after/commands.json](after/commands.json) retain actual argument vectors,
environment selection, exit codes and output files. Compiled observer binaries
are intentionally omitted. [source-identity.json](source-identity.json) binds
the changed production source files at this checkpoint.

## Observed compatibility

[comparison.json](comparison.json) records equality of all 25 observation exit
codes, stdout and stderr, and all five proposal byte sequences and SHA-256
digests. The ten profile observations include three finite source checks.
The five additional sources run native checks and one-qubit executions; their
proposal checks report producer consistency, not independently established
source meaning.

| Source boundary | Retained finite result | Retained sized result |
| --- | --- | --- |
| Unused import cycle | Reject at the closing import | Accept |
| Public or private same-module self-import | Reject collision or visibility | Accept |
| Module named `if` or `_` | Reject filesystem module name | Accept explicit map key |
| Unused foreign private import | Reject | Reject |
| Two declarations in one module | Retain and check both | Located one-function profile rejection |
| Duplicate declarations | Duplicate-name error | Existing one-function profile error first |
| Moved local shadows an imported callable | Reject; no declaration fallback | Reject; no declaration fallback |
| Same-module declaration call cycle | Recursive-call error | Existing one-function profile error first |

The proposal/execution cases cover two host-selected providers with the same
unqualified name in different modules, an imported call, and existing guarded
self-recursion instantiated at zero and two. No maximum-size quantum case was
generated or executed.

## Implementation scope

Both profiles consume collection-local `ModuleId`/`DefId` declarations from the
common source AST. Import and visibility lookup, iterative graph traversal and
finite topological ordering share one implementation. Finite caches use these
declaration IDs. Sized entry/provider selection fixes IDs before concrete
elaboration; elaboration consumes the resolved names rather than reconstructing
import strings. The projected sized AST no longer duplicates imports or public
visibility. Existing symbolic decrease, type, effect, owner and native gates
remain in their existing checkers.

IDs are not durable proof/evidence names. Canonical source paths, full retained
sources, static substitutions and provider instance identities remain attached
where previously required. The public source accessors, diagnostic bytes and
proposal payloads observed here are unchanged. Derived `Debug` output for
`ParsedProgram`, `Instantiation` and containers embedding them changes: it now
includes the private resolution table/IDs and omits redundant projected fields.
No stable serialized representation is promised by those Debug implementations.

Lexical owner/static-binder checking is not yet one complete resolved body AST.
The explicit finite/sized policies above, primitive support sets, source-loading
limits, and sized one-function restriction remain. This checkpoint does not
introduce general Basis parameters, new source syntax or broader profile
acceptance.

## Validation

[validation.json](validation.json) records the actual commands and scope:
171 distinct tests passed (135 integration tests and 36 frontend unit tests),
with nine existing ignores. Seven skips belong to explicit native-kernel lanes;
two preserve the historical 256-specialization/receipt work-limit stress cases
tracked in #274. The existing ownership differential test checked 4,000 cases.
No ignore was added. All-target Clippy with warnings denied, formatting,
whitespace checks and documentation links also passed. A test-authoring error
and its correction are recorded separately from production behavior.
