# Finite-leaf reconstruction attempt

The new `finite_leaf.rs.txt` source was saved before `cargo check --all-targets
--offline`. That first check failed with E0425/E0422 because the accompanying
verifier change used `QuantumPort` without adding its import. The missing
import was repaired; the first new module source remains unchanged here.

The immutable-byte and complete-output-port bindings are independently tested;
this record does not claim a Lean finite-leaf acceptance theorem or completed
production hierarchy. The full scope remains in the adjacent packet.
