import Qleisli.QirfValidity
import Qleisli.NativeContractWrapper
import Protocol.NativeContract

/-! Composition from the actual native-contract byte entry point to existing
root semantics and bounded encoded/leaf instrument semantics. These are QS components:
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
an assumed operator meaning. `check_encoded_sound` additionally exposes the
original operator correspondence for encoded requests. -/
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

/-- Independent meaning of the original bounded, closed, unitary root in an
encoded native request. The dependency interpretation is tied to a fresh graph
by `rootMeaning`; the encoded equation is about `actual`, not a ghost wrapper.
This proof summary admits no additional constitutional guarantee. -/
structure EncodedMeaning (artifact : QleisliKernel.Qirf.Artifact) (order : Array Nat)
    (root : QleisliKernel.Qirf.Validity.Root) (required : Contract)
    (actual : QleisliKernel.Semantics.Exact.Matrix) : Prop where
  rootMeaning : Qleisli.Qirf.Validity.RootMeaning artifact order root
  interface : artifact.rootInterface = some (required.input.physical,required.input.physical)
  classicalInputs : root.program.classicalInputs = []
  body : BodyMeaning root.dependencies root.program actual
  encoded : Qleisli.Semantics.Finite.Encoded actual required
  leftInverse : (Qleisli.Finite.square actual)ᴴ * Qleisli.Finite.square actual = 1
  rightInverse : Qleisli.Finite.square actual * (Qleisli.Finite.square actual)ᴴ = 1

/-- Success of the actual encoded request provides the original root's full
body meaning and encoded equation, retaining its complete Basis interface and
the continuous work states through root validation, reconstruction and checking. -/
theorem encoded_meaning {artifact : QleisliKernel.Qirf.Artifact} {order : Array Nat}
    {value : Lean.Json} {work left : Nat}
    (binding : EncodedAcceptance artifact order value work left) :
    ∃ root actual wrapper a b c,
      (QleisliKernel.Qirf.Validity.checkRoot artifact order).run binding.afterContract = (.ok root,a) ∧
      (QleisliKernel.Raw.BranchFunction.reconstruct root.dependencies root.program).run a = (.ok actual,b) ∧
      (QleisliKernel.Finite.wholeSpace actual).run b = (.ok (),c) ∧
      (QleisliKernel.Finite.check [⟨binding.required.input.physical,actual⟩]
        (QleisliKernel.Qirf.contractCircuit binding.required.input.physical)
        binding.required binding.required).run c = (.ok wrapper,left) ∧
      EncodedMeaning artifact order root binding.required actual := by
  obtain ⟨root,actual,wrapper,a,b,c,rootAccepted,interface,preflight,reconstructed,unitary,checked⟩ :=
    QleisliKernel.Qirf.checkContract_conditions _ _ _ _ _ binding.accepted
  have rootMeaning := Qleisli.Qirf.Validity.root_meaning _ _ _ _
    (QleisliKernel.Qirf.Validity.checkRoot_postcondition _ _ _ _ _ rootAccepted)
  have closed : root.program.classicalInputs = [] := by
    simp only [QleisliKernel.Raw.BranchFunction.preflight,Bool.and_eq_true,List.isEmpty_iff] at preflight
    exact preflight.1.1.1.2
  have body := Qleisli.Raw.BranchFunction.reconstruct_denotes _ _ closed _ _ _ reconstructed
  have encoded := Wrapper.check_encoded_original _ _ _ _ _ _ checked
  have inverses := Qleisli.Finite.wholeSpace_unitary _ _ _ unitary
  exact ⟨root,actual,wrapper,a,b,c,rootAccepted,reconstructed,unitary,checked,
    rootMeaning,interface,closed,body,encoded,inverses.1,inverses.2⟩

/-- Actual native-contract byte acceptance binds both request kinds to their
original-body meaning. The Acceptance witness retains the original bytes and
decoded request; this does not assert Rust/source/codec or compiled-I/O correctness. -/
theorem check_encoded_sound (bytes : ByteArray) (answer : Bool) (work left : Nat)
    (ok : (check bytes).run work = (.ok answer,left)) :
    ∃ binding : Acceptance bytes answer work left,
      match binding.request with
      | .encoded request => ∃ root actual,
          EncodedMeaning binding.artifact binding.order root request.required actual
      | .leaf request => request.actual = request.matrix ∧
          LeafMeaning binding.artifact binding.order request.root request.signature
            request.input request.output request.matrix := by
  obtain ⟨binding⟩ := check_acceptance _ _ _ _ ok
  refine ⟨binding,?_⟩
  cases binding.request with
  | encoded request =>
    obtain ⟨root,actual,_,_,_,_,_,_,_,_,meaning⟩ := encoded_meaning request
    exact ⟨root,actual,meaning⟩
  | leaf request => exact leaf_meaning request


/-- The accepted original root preserves the requested encoded action for an
arbitrary reference amplitude function, without a product-state assumption.
This does not add clean-release, runtime/export or compiler-preservation claims. -/
theorem encoded_reference {R : Type} {artifact : QleisliKernel.Qirf.Artifact} {order : Array Nat}
    {value : Lean.Json} {work left : Nat}
    (binding : EncodedAcceptance artifact order value work left) :
    ∃ root actual, EncodedMeaning artifact order root binding.required actual ∧
      ∀ (joint : Nat → R → ℂ) row reference, row < actual.rows →
        Qleisli.Semantics.Exact.action actual
          (fun index r => Qleisli.Semantics.Exact.action binding.required.input.map joint index r) row reference =
        Qleisli.Semantics.Exact.action binding.required.output.map
          (fun index r => Qleisli.Semantics.Exact.action binding.required.logical joint index r) row reference := by
  obtain ⟨root,actual,wrapper,a,b,c,_,_,_,checked,meaning⟩ := encoded_meaning binding
  exact ⟨root,actual,meaning,fun joint row reference bound =>
    Wrapper.check_reference_original _ _ _ _ _ _ checked joint row reference bound⟩

end Qleisli.NativeContract
