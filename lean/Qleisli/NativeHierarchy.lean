import Qleisli.Qirf
import Protocol.HierarchicalFinite

/-! Semantic discharge of every fresh native finite obligation. The actual
structural derivation composes these leaves, not Rust-reader assumptions.
Transport/compiler and general source preservation remain separate boundaries.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.NativeHierarchy
open QleisliKernel QleisliKernel.Hierarchical
open Protocol.HierarchicalFinite Qleisli.Semantics.ObservingFunction
open scoped Matrix

/-- Actual complete bytes, endpoints and original root instrument meaning.
No producer matrix or semantic receipt can inhabit this predicate by itself. -/
def LeafMeaning (request : Hierarchical.Finite.Request) : Prop :=
  ∃ required input output signature artifact order slots program a b,
    (matrix request.description).run a = (.ok required,b) ∧
    Hierarchical.Finite.unary request.physical.interface = true ∧
    request.physical.interface.inputs.quantum[0]? = some input ∧
    request.physical.interface.outputs.quantum[0]? = some output ∧
    artifact.rootInterface = some (signature,signature) ∧
    artifact.programs[artifact.root]? = some program ∧
    program.inputs = [⟨input.owner,input.axes.toList,Semantics.Finite.width signature⟩] ∧
    program.outputs = [output.owner] ∧
    Qirf.GraphDenotation artifact (Array.replicate artifact.entries.size none) order.toList slots ∧
    slots.all Option.isSome = true ∧
    BodyMeaning ((QleisliKernel.Qirf.before slots).map Semantics.ObservingFunction.Receipt.dependency) program required ∧
    (Qleisli.Finite.square required)ᴴ * Qleisli.Finite.square required = 1 ∧
    Qleisli.Finite.square required * (Qleisli.Finite.square required)ᴴ = 1 ∧
    (∃ c d, (Protocol.Qirf.read request.program).run c = (.ok (artifact,order),d))

theorem checkRequest_semantics (request : Hierarchical.Finite.Request) (work left : Nat)
    (ok : (checkRequest request).run work = (.ok (),left)) : LeafMeaning request := by
  obtain ⟨required,middle,description,leaf⟩ := checkRequest_conditions _ _ _ ok
  obtain ⟨input,output,signature,artifact,order,a,b,c,d,unary,hi,ho,_,decoded,root⟩ :=
    checkLeaf_conditions _ _ _ _ _ leaf
  obtain ⟨slots,program,checked,graph,full,header,found,inputs,outputs,_,meaning,unitary⟩ :=
    Qirf.reconstruct_semantics _ _ _ _ _ _ _ _ root
  exact ⟨required,input,output,signature,artifact,order,slots,program,work,middle,
    description,unary,hi,ho,header,found,inputs,outputs,graph,full,meaning,unitary.1,unitary.2,b,c,decoded⟩

/-- All original finite requests, including shared non-root and zero-repeat
dependencies, receive semantic discharge from the native pass itself. -/
theorem checkLeaves_semantics (requests : Array Hierarchical.Finite.Request) (work left : Nat)
    (ok : (checkLeaves requests).run work = (.ok (),left)) :
    ∀ request ∈ requests.toList, LeafMeaning request := by
  intro request member
  obtain ⟨a,b,checked⟩ := checkLeaves_each _ _ _ ok request member
  exact checkRequest_semantics _ _ _ checked

theorem conditional_derives (artifact : Artifact.Artifact) (order : Array Nat)
    (pending : Conditional.Pending) (work left : Nat)
    (accepted : Conditional.checkAll artifact order = .ok pending)
    (native : (checkLeaves pending.state.requests).run work = (.ok (),left)) :
    Conditional.Derives artifact LeafMeaning artifact.entry.proof :=
  (Conditional.checkAll_conditions _ _ _ accepted).2.2.2.2 LeafMeaning
    (checkLeaves_semantics _ _ _ native)

/-- Every independent finite root/provider pair has one identical complete
decoded matrix. The structural pass, not the caller, determines the list. -/
theorem requested_pairs (artifact : Artifact.Artifact) (request : Root.Request)
    (pairs : Array Root.Pair) (indices : List Nat) (work left : Nat)
    (ok : (checkPairs artifact request pairs indices).run work = (.ok (),left)) :
    indices = Root.obligations artifact request pairs ∧
      ∀ index ∈ indices, ∃ pair actual a b c,
        Root.finitePair artifact request pairs index = some pair ∧
        (matrix pair.left).run a = (.ok actual,b) ∧ (matrix pair.right).run b = (.ok actual,c) := by
  obtain ⟨bound,each⟩ := checkPairs_each _ _ _ _ _ _ ok
  refine ⟨bound,?_⟩
  intro index member
  obtain ⟨a,b,checked⟩ := each index member
  exact checkPair_conditions _ _ _ _ _ _ checked

/-- The fixed H role denotes the original root body, including its phase,
not just the producer's declared finite matrix or a basis probability table. -/
theorem hadamard_semantics (artifact : Artifact.Artifact) (index work left : Nat)
    (ok : (checkHadamard artifact hadamard index).run work = (.ok (),left)) :
    ∃ definition bytes signature decoded order slots program input output,
      artifact.definitions[index]? = some definition ∧ definition.body = .leaf bytes ∧
      definition.effect = .unitary ∧
      definition.interface.inputs.quantum[0]? = some input ∧
      definition.interface.outputs.quantum[0]? = some output ∧
      (∃ a b, (Protocol.Qirf.read bytes).run a = (.ok (decoded,order),b)) ∧
      decoded.rootInterface = some (signature,signature) ∧
      decoded.programs[decoded.root]? = some program ∧
      program.inputs = [⟨input.owner,input.axes.toList,Semantics.Finite.width signature⟩] ∧
      program.outputs = [output.owner] ∧
      Qirf.GraphDenotation decoded (Array.replicate decoded.entries.size none) order.toList slots ∧
      slots.all Option.isSome = true ∧
      BodyMeaning ((QleisliKernel.Qirf.before slots).map Semantics.ObservingFunction.Receipt.dependency)
        program hadamard := by
  obtain ⟨definition,bytes,a,found,body,effect,leaf⟩ := checkHadamard_conditions _ _ _ _ _ ok
  obtain ⟨input,output,signature,decoded,order,b,c,d,e,_,hi,ho,_,read,root⟩ :=
    checkLeaf_conditions _ _ _ _ _ leaf
  obtain ⟨slots,program,_,graph,full,header,present,inputs,outputs,_,meaning,_⟩ :=
    Qirf.reconstruct_semantics _ _ _ _ _ _ _ _ root
  exact ⟨definition,bytes,signature,decoded,order,slots,program,input,output,
    found,body,effect,hi,ho,⟨c,d,read⟩,header,present,inputs,outputs,graph,full,meaning⟩

theorem checkHadamards_semantics (artifact : Artifact.Artifact) (indices : List Nat) (work left : Nat)
    (ok : (checkHadamards artifact indices).run work = (.ok (),left)) :
    ∀ index ∈ indices, ∃ a b,
      (checkHadamard artifact hadamard index).run a = (.ok (),b) ∧
      ∃ definition bytes signature decoded order slots program input output,
        artifact.definitions[index]? = some definition ∧ definition.body = .leaf bytes ∧
        definition.effect = .unitary ∧
        definition.interface.inputs.quantum[0]? = some input ∧
        definition.interface.outputs.quantum[0]? = some output ∧
        (∃ c d, (Protocol.Qirf.read bytes).run c = (.ok (decoded,order),d)) ∧
        decoded.rootInterface = some (signature,signature) ∧
        decoded.programs[decoded.root]? = some program ∧
        program.inputs = [⟨input.owner,input.axes.toList,Semantics.Finite.width signature⟩] ∧
        program.outputs = [output.owner] ∧
        Qirf.GraphDenotation decoded (Array.replicate decoded.entries.size none) order.toList slots ∧
        slots.all Option.isSome = true ∧
        BodyMeaning ((QleisliKernel.Qirf.before slots).map Semantics.ObservingFunction.Receipt.dependency)
          program hadamard := by
  intro index member
  obtain ⟨a,b,checked⟩ := checkHadamards_each _ _ _ _ ok index member
  exact ⟨a,b,checked,hadamard_semantics _ _ _ _ checked⟩

end Qleisli.NativeHierarchy
