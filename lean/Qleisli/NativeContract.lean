import Qleisli.QirfValidity
import Protocol.NativeContract

/-! Composition from the actual native-contract byte entry point to existing
root semantics and bounded leaf instrument semantics. These are QS components:
source/compiler preservation, emitted target correctness and quantitative RS
are separate obligations. No guarantee admission follows from these lemmas.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.NativeContract
open QleisliKernel QleisliKernel.Protocol.NativeContract
open QleisliKernel.Semantics.Finite QleisliKernel.Semantics.ObservingFunction
open Qleisli.Semantics.ObservingFunction
open scoped Matrix

/-- Either request kind validates the original root with the production
checker. The encoded branch's finite wrapper result is not identified with the
original root operator by this theorem. -/
theorem acceptance_root_meaning {bytes : ByteArray} {answer : Bool} {work left : Nat}
    (binding : Acceptance bytes answer work left) :
    ∃ root a b,
      (QleisliKernel.Qirf.Validity.checkRoot binding.artifact binding.order).run a = (.ok root,b) ∧
      Qleisli.Qirf.Validity.RootMeaning binding.artifact binding.order root := by
  cases binding.request with
  | encoded request =>
    obtain ⟨root,actual,a,b,c,d,result,last,accepted,_,_,_⟩ :=
      QleisliKernel.Qirf.checkContract_bound _ _ _ _ _ request.accepted
    exact ⟨root,request.afterContract,a,accepted,
      Qleisli.Qirf.Validity.root_meaning _ _ _ _
        (QleisliKernel.Qirf.Validity.checkRoot_postcondition _ _ _ _ _ accepted)⟩
  | leaf request =>
    exact ⟨request.root,request.afterMatrix,request.afterRoot,request.rootAccepted,
      Qleisli.Qirf.Validity.root_meaning _ _ _ _
        (QleisliKernel.Qirf.Validity.checkRoot_postcondition _ _ _ _ _ request.rootAccepted)⟩

theorem check_root_meaning (bytes : ByteArray) (answer : Bool) (work left : Nat)
    (ok : (check bytes).run work = (.ok answer,left)) :
    ∃ binding : Acceptance bytes answer work left,
      ∃ root a b,
        (QleisliKernel.Qirf.Validity.checkRoot binding.artifact binding.order).run a = (.ok root,b) ∧
        Qleisli.Qirf.Validity.RootMeaning binding.artifact binding.order root := by
  obtain ⟨binding⟩ := check_acceptance _ _ _ _ ok
  exact ⟨binding,acceptance_root_meaning binding⟩

/-- Full original-body instrument meaning for the bounded, closed, unitary
leaf fragment. Equality uses the exact requested complex matrix, retaining
phase, tuple signature and ordered input/output ports. The live output is tied
to an actual verification, not an unconstrained checked-state witness. -/
structure LeafMeaning (artifact : QleisliKernel.Qirf.Artifact) (order : Array Nat)
    (root : QleisliKernel.Qirf.Validity.Root) (signature : Basis)
    (input output : QleisliKernel.Semantics.Raw.Port) (matrix : Semantics.Exact.Matrix) : Prop where
  rootMeaning : Qleisli.Qirf.Validity.RootMeaning artifact order root
  interface : artifact.rootInterface = some (signature,signature)
  inputs : root.program.inputs = [input]
  outputs : root.program.outputs = [output.token]
  classicalInputs : root.program.classicalInputs = []
  classicalOutputs : root.program.classicalOutputs = []
  effect : root.program.effect = .unitary
  instrument : ∃ slots,
    Qleisli.Qirf.GraphDenotation artifact (Array.replicate artifact.entries.size none) order.toList slots ∧
    slots.all Option.isSome = true ∧
    BodyMeaning ((QleisliKernel.Qirf.before slots).map Receipt.dependency) root.program matrix ∧
    ∃ checked a b,
      (QleisliKernel.Raw.Observation.verify
        ((QleisliKernel.Qirf.before slots).map Receipt.dependency) root.program).run a = (.ok checked,b) ∧
      checked.state.quantum.live = [output]
  leftInverse : (Qleisli.Finite.square matrix)ᴴ * Qleisli.Finite.square matrix = 1
  rightInverse : Qleisli.Finite.square matrix * (Qleisli.Finite.square matrix)ᴴ = 1

theorem leaf_meaning {artifact : QleisliKernel.Qirf.Artifact} {order : Array Nat}
    {value : Lean.Json} {work left : Nat}
    (binding : LeafAcceptance artifact order value work left) :
    binding.actual = binding.matrix ∧
      LeafMeaning artifact order binding.root binding.signature binding.input binding.output binding.matrix := by
  have root := Qleisli.Qirf.Validity.root_meaning _ _ _ _
    (QleisliKernel.Qirf.Validity.checkRoot_postcondition _ _ _ _ _ binding.rootAccepted)
  obtain ⟨same,a,b,reconstructed⟩ := Qleisli.Qirf.check_semantics _ _ _ _ _ _ _ _ _ binding.accepted
  obtain ⟨deps,program,checked,c,d,e,f,g,h,i,j,graph,interface,present,
      inputs,outputs,closedInputs,closedOutputs,effect,verified,live,body,unitary⟩ :=
    QleisliKernel.Qirf.reconstruct_conditions _ _ _ _ _ _ _ _ reconstructed
  have original : program = binding.root.program := Option.some.inj (present.symm.trans root.original)
  obtain ⟨slots,graphMeaning,full,bound⟩ := Qleisli.Qirf.checkGraph_semantics _ _ _ _ _ graph
  have meaning := Qleisli.Raw.BranchFunction.reconstruct_denotes _ _ closedInputs _ _ _ body
  have inverses := Qleisli.Finite.wholeSpace_unitary _ _ _ unitary
  rw [original,bound] at meaning verified
  exact ⟨same,root,interface,original ▸ inputs,original ▸ outputs,original ▸ closedInputs,
    original ▸ closedOutputs,original ▸ effect,
    ⟨slots,graphMeaning,full,meaning,checked,e,f,verified,live⟩,inverses.1,inverses.2⟩

/-- Arbitrary finite references are included without separability or
normalization premises. These whole-space inverse laws alone do not assert
clean release, source preservation or target execution correctness. -/
theorem leaf_reference_laws {R : Type} [Fintype R] [DecidableEq R]
    {artifact : QleisliKernel.Qirf.Artifact} {order : Array Nat}
    {value : Lean.Json} {work left : Nat}
    (binding : LeafAcceptance artifact order value work left) :
    let joint := _root_.Matrix.kronecker (Qleisli.Finite.square binding.matrix) (1 : _root_.Matrix R R ℂ)
    jointᴴ * joint = 1 ∧ joint * jointᴴ = 1 := by
  have first := HierarchicalUnitary.reference_isometry (R := R) _ (leaf_meaning binding).2.leftInverse
  exact ⟨first,mul_eq_one_comm.mp first⟩

/-- The native success premise supplies the request binding. The leaf result
is conditional only on the decoded request kind, not on a producer receipt or
an assumed operator meaning. Encoded operator correspondence remains separate. -/
theorem check_sound (bytes : ByteArray) (answer : Bool) (work left : Nat)
    (ok : (check bytes).run work = (.ok answer,left)) :
    ∃ binding : Acceptance bytes answer work left,
      (∃ root a b,
        (QleisliKernel.Qirf.Validity.checkRoot binding.artifact binding.order).run a = (.ok root,b) ∧
        Qleisli.Qirf.Validity.RootMeaning binding.artifact binding.order root) ∧
      match binding.request with
      | .encoded _ => True
      | .leaf request => request.actual = request.matrix ∧
          LeafMeaning binding.artifact binding.order request.root request.signature
            request.input request.output request.matrix := by
  obtain ⟨binding⟩ := check_acceptance _ _ _ _ ok
  refine ⟨binding,acceptance_root_meaning binding,?_⟩
  cases binding.request with
  | encoded request => trivial
  | leaf request => exact leaf_meaning request

end Qleisli.NativeContract
