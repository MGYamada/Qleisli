# Provider descriptions and literal terminal resources

Each file was written before its first run with the shared
[project manifest](Qargo.toml). Copy the selected source to `main.qli` and
use `qleisli interop emit-qasm <project> --input=qli --resources`. The
retained responses came from the candidate
`c4a3a6170307a472605797890653e6006ec756b8` with native Lean 4.30.0.

| Original source | First target response | Checked result |
| --- | --- | --- |
| [Composition with the inverse](composed-inverse.qli) | [Target response](composed-inverse-target.json) | Zero emitted gates after exact phase cancellation |
| [Power of the inverse](inverse-power.qli) | [Target response](inverse-power-target.json) | One S-dagger gate for two negative eighth turns |
| [Ordered tensor](ordered-tensor.qli) | [Target response](ordered-tensor-target.json) | T on the left axis and T-dagger on the right axis |
| [Uncontrolled scalar provider](unsupported-phase.qli) | [Target refusal](unsupported-phase-target.json) | The actual scalar is outside the terminal gate vocabulary |

The last [source check](unsupported-phase-check.json) accepts the typed
original program, including its resolved applicable provider and zero-width
owner. The terminal refusal returns no resource report. The companion
`terminal_workspace_resources_follow_the_selected_provider` and
`terminal_workspace_resources_bind_the_declared_controlled_phase` tests
cover a changed provider cost and a controlled phase. These examples are
limited to the checked terminal profile and use small registers.
