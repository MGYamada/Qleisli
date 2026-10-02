# rotation_half_y

Translation of `circuit(params)` from the [frozen source](https://github.com/PennyLaneAI/demos/blob/3a04df83a16af3a2f0fd9398c0b5cc2c060ebedd/demonstrations_v2/tutorial_qubit_rotation/demo.py); `Apache-2.0`. Original notices and [permission records](../../POLICY.md) apply.

Contract: RY(pi) RX(pi/2)=[[i,-1],[1,-i]]/sqrt(2), in upstream gate order with exact scalar phase.

`kernel` consumes and returns every input owner; left-to-right leaves are low-weight first. `main` starts from [0] and measures each returned leaf in Z.

Scope: Fix params=(pi/2,pi); gate kernel only. Excludes optimization and a continuous-angle API; main measures Z.

[Authoring](../../authoring/v026-small/README.md) retains first source/checks. Independent analytic full-entry X/Y interference checks every input and output coefficient, including phase; the paired `half_rotation_order_reversed` fault must typecheck and disagree. Numerical tolerance is 1e-11; this is finite validation, not a translation proof, upstream-framework execution or model benchmark.
