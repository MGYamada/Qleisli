# qaoa_path_layer3

[U_C; U_B](https://github.com/PennyLaneAI/demos/blob/3a04df83a16af3a2f0fd9398c0b5cc2c060ebedd/demonstrations_v2/tutorial_qaoa_maxcut/demo.py), frozen Apache-2.0 input; [license](../../upstream/pennylane_demos/LICENSE).

RX(pi/2)^tensor3 exp(-i*pi*(Z0 Z1+Z1 Z2)/4), gamma=pi/2, beta=pi/4, cost then mixer. The middle wire belongs to both edges.

Narrow the four-node graph to path edges (0,1),(1,2), retaining one whole cost/mixer layer on three arbitrary inputs. No initial H, full MaxCut port or optimizer.

The first QLI leaf is the low bit; output measurements follow leaf order. Every input owner is returned; no implicit discard or postselection. Complete complex columns are compared by X/Y interference at tolerance 1e-11, including coherent control. The paired fault tests omit the second edge while retaining the shared middle wire. Numerical agreement is not a translation proof; upstream frameworks are not executed.

[First sources and diagnostics](../../authoring/v028-small/README.md).
