# ising_zz_negative2

Translation of `U_C(gamma), single-edge factor` from the [frozen source](https://github.com/PennyLaneAI/demos/blob/3a04df83a16af3a2f0fd9398c0b5cc2c060ebedd/demonstrations_v2/tutorial_qaoa_maxcut/demo.py); `Apache-2.0`. Original notices and [permission records](../../POLICY.md) apply.

Contract: exp(+i*pi*Z0*Z1/4), gamma=-pi/2; diagonal coefficient exp(+i*pi*(-1)^(a+b)/4) for each basis input.

`kernel` consumes and returns every input owner; left-to-right leaves are low-weight first. `main` starts from [0, 1] and measures each returned leaf in Z.

Scope: One isolated edge of the original graph; no mixer, preparation, optimizer or complete QAOA port. Includes the RZ scalar under an extra control.

[Authoring](../../authoring/v026-small/README.md) retains first source/checks. Independent analytic full-entry X/Y interference checks every input and output coefficient, including phase; the paired `negative_zz_missing_scalar` fault must typecheck and disagree. Numerical tolerance is 1e-11; this is finite validation, not a translation proof, upstream-framework execution or model benchmark.
