# Original shared-control order probes

Two CNOTs share `ctrl q[1]` and update disjoint exclusive targets `q[0]`
and `q[2]`. In either order their exact action flips both targets when the
control is one. The second source applies Z to the first target on opposite
sides of the CNOT. Its two orders differ by a sign in the control-one sector,
which computational-basis probabilities alone cannot detect.

The first four Raw checks passed, and the same selected hierarchy entries
refused the then-unsupported control path. These CLI observations are
separate from the independent whole-space matrix checks. The exact matrix
entries fix the action tensored with an arbitrary reference. A local
conformance check does not authorize a source reorder or derive a general
footprint theorem. Saved CLI commands are inert.
