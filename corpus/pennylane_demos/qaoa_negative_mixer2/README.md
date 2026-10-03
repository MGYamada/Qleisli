# qaoa_negative_mixer2

[U_B](https://github.com/PennyLaneAI/demos/blob/3a04df83a16af3a2f0fd9398c0b5cc2c060ebedd/demonstrations_v2/tutorial_qaoa_maxcut/demo.py), frozen Apache-2.0 input; [license](../../upstream/pennylane_demos/LICENSE).

U_B(-pi/4)=RX(-pi/2) tensor RX(-pi/2); U[y,x]=i^popcount(x xor y)/2.

Two-wire mixer only; no cost layer, state preparation, graph optimizer or sampling claim.

The first QLI leaf is the low bit; output measurements follow leaf order. Every input owner is returned; no implicit discard or postselection. Complete complex columns are compared by X/Y interference at tolerance 1e-11, including coherent control. The paired fault tests use positive beta in both rotations; basis probabilities agree. Numerical agreement is not a translation proof; upstream frameworks are not executed.

[First sources and diagnostics](../../authoring/v028-small/README.md).
