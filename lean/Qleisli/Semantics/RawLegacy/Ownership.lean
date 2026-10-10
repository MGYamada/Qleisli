import Qleisli.Semantics.RawLegacy.Observation
import QleisliKernel.Semantics.Ownership

/-! Pre-Unit-opcode semantic fragment for checked representation transport.
Extracted from `lean-kernel/QleisliKernel/Semantics/Ownership.lean` at `bb28608599e5df86b485ad5ff369e22d97a51ae6`
(SHA-256 `ad6db263fa43f9290e0d4d2b0c5a1883b367b14ca260e9717a8c2893a2f37b95`). Only imports, namespaces and
references to shared unchanged definitions differ. There is no checker here.
Stable payloads/states/rules are shared; their historical identity must still be checked.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Semantics.RawLegacy.Ownership
open QleisliKernel.Semantics.Raw QleisliKernel.Semantics.Ownership
open Observation

/-- Issued outputs of the original instruction, including all protected targets. -/
def outputs : Raw.Op → List Nat
  | .init0 out _ | .gate _ _ out | .join _ _ out | .liftBasis _ out _ _
  | .applyUnitary _ out _ | .certifiedCompute _ out _ _ _ _ => [out]
  | .cnot _ _ a b | .quantumIf _ _ a b _ _ | .split _ a b _ => [a,b]
  | .toffoli _ _ _ a b c => [a,b,c]
  | .computeUseUncompute _ out targets _ _ _ => out :: targets.map (·.output)

/-- Scratch identities remain issued after their scoped operation. Fresh axes
of a lift are the suffix after its original operand, not inferred separability. -/
def allocated (state : State) : Raw.Op → List Nat
  | .init0 _ wire => [wire]
  | .liftBasis input _ wires _ =>
    wires.drop (((state.live.find? (fun port => port.token == input)).map (·.bits)).getD 0)
  | .certifiedCompute _ _ ancilla _ _ _ | .computeUseUncompute _ _ _ ancilla _ _ => ancilla
  | _ => []

/-- Shape and access obligations on the literal original operation. Internal
circuits borrow only local coordinates; scratch release equations are separate. -/
def Access (state : State) : Raw.Op → Prop
  | .init0 _ _ | .join _ _ _ => True
  | .gate _ input _ => BitOwner state input
  | .cnot control target _ _ => BitOwner state control ∧ BitOwner state target
  | .toffoli a b target _ _ _ => BitOwner state a ∧ BitOwner state b ∧ BitOwner state target
  | .quantumIf control target _ _ zero one => BitOwner state control ∧
    ∃ port, PortAt state target port ∧ Circuit port.bits (zero.map QleisliKernel.Semantics.RawTrace.unitary) ∧
      Circuit port.bits (one.map QleisliKernel.Semantics.RawTrace.unitary)
  | .split input _ _ left => ∃ port, PortAt state input port ∧ left ≤ port.bits
  | .liftBasis input _ wires _ => ∃ port, PortAt state input port ∧
    port.bits ≤ wires.length ∧ wires.take port.bits = port.wires
  | .applyUnitary input _ steps => ∃ port, PortAt state input port ∧ Circuit port.bits steps
  | .certifiedCompute input _ scratch _ physical logical => ∃ port, PortAt state input port ∧
    Circuit (port.bits + scratch.length) physical ∧ Circuit port.bits logical
  | .computeUseUncompute input _ targets scratch _ uses => ∃ port, PortAt state input port ∧
    (∀ target ∈ targets, BitOwner state target.input) ∧ Uses port.bits scratch.length targets.length uses

/-- Literal consumption/return is fixed by the independent original-operation
reader. Exact issued lists plus Valid rule out every reuse, including scratch. -/
structure Pure (before : State) (op : Raw.Op) (after : State) : Prop where
  access : Access before op
  action : ∃ events, RawTrace.step before.interface op = some (after.interface,events)
  tokens : after.tokens = before.tokens ++ outputs op
  wires : after.wires = before.wires ++ allocated before op

mutual
  /-- Both classical arms are certified from the same live entry. Their issued
  identity store is threaded globally, even when only one arm will execute. -/
  inductive Step : State → Observation.Op → State → Prop
    | pure (before op after) (body : Pure before op after) : Step before (.pure op) after
    | measure (before input output port after) (body : Erase before input port after)
        (bit : port.bits = 1) : Step before (.measure input output) after
    | reset (before input output wire port middle after) (body : Erase before input port middle)
        (bit : port.bits = 1) (fresh : Input middle ⟨output,[wire],1⟩ after) :
        Step before (.reset input output wire) after
    | discard (before input port after) (body : Erase before input port after) :
        Step before (.discard input) after
    | constant (state value output) : Step state (.constant value output) state
    | not (state input output) : Step state (.not input output) state
    | xor (state left right output) : Step state (.xor left right output) state
    | and (state left right output) : Step state (.and left right output) state
    | branch (before condition thenOps elseOps quantum classical left right after)
        (thenArm : Run before thenOps left)
        (elseArm : Run (restore before left) elseOps right)
        (coverage : Phi left right quantum)
        (merge : Inputs (mergeBase right) (phiPorts quantum) after) :
        Step before (.branch condition thenOps elseOps quantum classical) after
  /-- Every instruction boundary in both arms is valid; this includes every
  list prefix and not only the final returned state. -/
  inductive Run : State → List Observation.Op → State → Prop
    | nil (state) (valid : Valid state) : Run state [] state
    | cons (before op middle ops after) (valid : Valid before)
        (head : Step before op middle) (tail : Run middle ops after) :
        Run before (op :: ops) after
end

/-- Linear ownership safety for a complete ordinary raw program. Classical
SSA/effect correctness, quantum cleanup meaning, costs and hierarchy are separate. -/
def OwnershipSafe (program : Observation.Program) : Prop :=
  ∃ initial final, Inputs {} program.inputs initial ∧
    Run initial program.operations final ∧ Returned final program.outputs


end Qleisli.Semantics.RawLegacy.Ownership
