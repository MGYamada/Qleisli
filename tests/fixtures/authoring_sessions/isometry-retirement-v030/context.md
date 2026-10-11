# Isometry prefix retirement control

Curated source migration under the adopted #57 naming decision, authored by the
Codex assistant with the repository and earlier isometry tests already visible.
No external model or blind benchmark is involved. The two complete sources are
frozen before checking: the first uses legacy `iso`, the second changes only
that prefix to `isometry`. Both should initially prepare and measure zero; after
the cutover the first must report a located migration error and the second must
retain the checked effect, owner behavior and zero outcome. Fixed transport tags
remain `iso`. These observations are not an exact source-preservation proof.
