import QleisliKernel.Semantics.Raw

/-! Pre-Unit-opcode semantic fragment for checked representation transport.
Extracted from `lean-kernel/QleisliKernel/Semantics/Raw.lean` at `bb28608599e5df86b485ad5ff369e22d97a51ae6`
(SHA-256 `e2af2ae0379f5a4f22e19170fd0d3ef532da2dd7d0e636202e5e77d38ce990cf`). Only imports, namespaces and
references to shared unchanged definitions differ. There is no checker here.
Stable payloads/states/rules are shared; their historical identity must still be checked.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Semantics.RawLegacy.Raw
open QleisliKernel.Semantics.Raw QleisliKernel.Semantics.Finite

inductive Op where
  | init0 (output wire : Nat)
  | gate (gate : Gate) (input output : Nat)
  | cnot (control target controlOut targetOut : Nat)
  | toffoli (a b target aOut bOut targetOut : Nat)
  | quantumIf (control target controlOut targetOut : Nat) (zero one : List UnitaryStep)
  | split (input left right leftBits : Nat)
  | join (left right output : Nat)
  | liftBasis (input output : Nat) (wires table : List Nat)
  | applyUnitary (input output : Nat) (steps : List Step)
  | certifiedCompute (input output : Nat) (ancilla function : List Nat)
      (useSteps logicalSteps : List Step)
  | computeUseUncompute (input output : Nat) (targets : List Target)
      (ancilla function : List Nat) (uses : List Use)
  deriving BEq, DecidableEq, Repr

structure Program where
  inputs : List Port
  operations : List Op
  outputs : List Nat
  effect : Effect
  deriving BEq, DecidableEq, Repr

/-- Raw bodies, including original signatures, are reconstructed before calls.
No computed circuit, matrix, private identity or accepted flag is supplied. -/
structure Evidence where
  signature : Basis
  implementation : Program
  specification : Program
  deriving BEq, DecidableEq, Repr


end Qleisli.Semantics.RawLegacy.Raw
