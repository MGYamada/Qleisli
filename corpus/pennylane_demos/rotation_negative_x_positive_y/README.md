# rotation_negative_x_positive_y

[circuit(params)](https://github.com/PennyLaneAI/demos/blob/3a04df83a16af3a2f0fd9398c0b5cc2c060ebedd/demonstrations_v2/tutorial_qubit_rotation/demo.py), frozen Apache-2.0 input; [license](../../upstream/pennylane_demos/LICENSE).

RY(pi/2) RX(-pi/2), params=(-pi/2,pi/2); matrix [[1-i,-1+i],[1+i,1+i]]/2, including scalar phase.

Fixed exact angles and full operator; no optimization, arbitrary-angle API or expectation-only comparison.

The first QLI leaf is the low bit; output measurements follow leaf order. Every input owner is returned; no implicit discard or postselection. Complete complex columns are compared by X/Y interference at tolerance 1e-11, including coherent control. The paired fault tests reverse the noncommuting rotations. Numerical agreement is not a translation proof; upstream frameworks are not executed.

[First sources and diagnostics](../../authoring/v028-small/README.md).
