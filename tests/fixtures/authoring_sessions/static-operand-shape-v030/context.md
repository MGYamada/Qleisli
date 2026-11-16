# Static operation operand diagnostic

Informed regression for #272. Adapt its original nesting example to the
current operation application syntax. A static control provider expects
`Q<((Bit,Bit),Bit)>` and the caller supplies `Q<(Bit,(Bit,Bit))>`.
The leaves agree in order, but the interface requires the exact declared tree.
The argument is intentionally invalid. The diagnostic should identify that
argument and show the two complete types in expected and actual order.

The baseline source checkout is main at `a844010f`. Baseline observations use
an existing local beta CLI binary built before the diagnostic changes in this
worktree. Its path and digest identify the binary. Its exact source commit was
not established.
