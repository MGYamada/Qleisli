import QleisliKernel.Raw.ObservationAgreement

/-! A proof-local factor of the actual independent reader. Its successor
equation retains every constructor, branch and phi permutation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw.ObservationAgreement
open QleisliKernel QleisliKernel.Semantics.Finite

def readStep (recurse : Reader) (state : Interface) (op : Op) : Option Result :=
  match op with
  | .pure operation => do
    let (next,added) ← Semantics.RawTrace.step state operation
    pure (next,added.map Semantics.Observation.Event.pure)
  | .measure input output => do
    let (port,next) ← Semantics.RawTrace.take state input
    pure ({next with frame := Semantics.Observation.remaining state port.wires},
      [.erase state.frame.length (Semantics.RawTrace.axes state port.wires) (some output)])
  | .discard input => do
    let (port,next) ← Semantics.RawTrace.take state input
    pure ({next with frame := Semantics.Observation.remaining state port.wires},
      [.erase state.frame.length (Semantics.RawTrace.axes state port.wires) none])
  | .reset input output wire => do
    let (port,next) ← Semantics.RawTrace.take state input
    let frame := Semantics.Observation.remaining state port.wires
    pure ({Semantics.RawTrace.insert next output [wire] with frame := frame ++ [wire]},
      [.erase state.frame.length (Semantics.RawTrace.axes state port.wires) none,.pure (.init0 frame.length)])
  | .constant value output => pure (state,[.classical (.constant value) output])
  | .not input output => pure (state,[.classical (.not input) output])
  | .xor left right output => pure (state,[.classical (.xor left right) output])
  | .and left right output => pure (state,[.classical (.and left right) output])
  | .branch condition thenOps elseOps quantum classical => do
    let (left,leftEvents) ← recurse state thenOps
    let (right,rightEvents) ← recurse state elseOps
    let finish := fun (arm : Interface) (choice : Bool) =>
      Semantics.Observation.Event.pure (.reorder arm.frame.length
        (Semantics.RawTrace.axes arm (Semantics.Observation.phiWires arm quantum choice)))
    pure (Semantics.Observation.phiInterface quantum,
      [.branch condition (leftEvents ++ [finish left true]) (rightEvents ++ [finish right false]) classical])

def layer (recurse : Reader) (initial : Interface) (operations : List Op) : Option Result :=
  operations.foldlM (fun (state,events) op => do
    let (next,added) ← readStep recurse state op
    pure (next,events ++ added)) (initial,[])

theorem read_succ (fuel : Nat) (initial : Interface) (operations : List Op) :
    Semantics.Observation.readOps (fuel+1) initial operations =
      layer (Semantics.Observation.readOps fuel) initial operations := by
  unfold Semantics.Observation.readOps layer
  apply QleisliKernel.Raw.DependencyTransport.fold_same
  intro op member before
  rcases before with ⟨state,events⟩
  cases op <;> first
  | rfl
  | simp [readStep,Option.bind_assoc]

def OneAgrees (left right : List Dependency) (fuel : Nat) : Op → Prop
  | .pure operation => QleisliKernel.Raw.RawAgreement.OpAgrees left right operation
  | .branch _ zero one _ _ => OpsAgree left right fuel zero ∧ OpsAgree left right fuel one
  | _ => True

end QleisliKernel.Raw.ObservationAgreement
