# Shared-wiring first attempts

Informed development on 2026-09-29, following the [bounded packet](../wiring-packet.md).
No new `.qli` syntax or additional external corpus source is introduced.

The first [pure inspector](Wiring.lean.txt) and [diagnostics](compile.txt) retain
an unavailable Option flatten name, unavailable pure-package tactic and array
lookup lemma repairs. The repaired source uses ordinary total folds and cache
updates; the runtime policy is unchanged.

The [initial complex algebra](HierarchicalWiring.lean.txt) and
[diagnostics](math-compile.txt) retain finite list-index and lemma application
repairs. The [first full binding source](binding.lean.txt) and
[diagnostics](binding-compile.txt) retain dependent width-cast and Option/list
normalization repairs. The final proof constructs actual evaluation from the
fresh derivation; it assumes no semantic cache or finite-leaf matrix equation.

The first [native source](native.lean.txt), [fixture](test_hierarchical_wiring.py.txt),
[observed output](../wiring-native-first.json) and [diagnostics](native-diagnostics.txt)
retain a wrong fixture expectation: removing the first selected node removed an
independent requested rename, not another node's dependency. The component
correctly returned a cache without that root. The corrected fixture removes an
actual tensor child and requires rejection. Callers must require the root's
presence before using a computed route. The [final native record](../wiring-native.json)
adds explicit cases showing that axis routing alone cannot certify duplicated
axes or coverage of an empty owner; actual node typing rejects both.

Copyright 2026 Masahiko G. Yamada. Apache-2.0.
