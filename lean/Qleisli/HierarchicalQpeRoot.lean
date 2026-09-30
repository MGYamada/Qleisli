import Qleisli.HierarchicalProvider
import QleisliKernel.Hierarchical.QpeRoot

/-! Provider semantics from the single fresh QPE root check.
The independent requested graph is interpreted by its own finite reader; exact
finite equations remain the stated transitional integration obligations.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.HierarchicalQpeRoot
open QleisliKernel.Hierarchical
open Artifact HierarchicalFiniteEvaluation HierarchicalOperators HierarchicalTyping

/-- Full header validation and the sized provider boundary determine both
physical dimensions. A producer's register name alone does not establish them. -/
theorem checkAll_provider_widths (request : QpeRoot.Request) (packet : QpeRoot.Packet)
    (pending : QpeRoot.Pending) (accepted : QpeRoot.checkAll request packet = .ok pending)
    (value : Operator) (unitary : UnitaryInterface request.provider.interface value) :
    value.inputWidth = request.circuit.target.size ∧
      value.outputWidth = request.circuit.target.size := by
  have stages := QpeRoot.checkAll_conditions request packet pending accepted
  have facts := QpeRoot.assemble_conditions request packet pending.artifact pending stages.2
  have typed := (Conditional.checkAll_conditions _ _ _ stages.1).1
  have nodes := (ContractTyping.checkAll_conditions _ _ _ typed).1
  have prepared := (NodeTyping.checkAll_conditions _ _ _ nodes).1
  have headers := Artifact.prepare_headers _ _ _ prepared
  have bound := Root.inspect_conditions _ _ _ _ _ _ facts.2.2.2.1
  obtain ⟨d,p,first,foundD,_,_,_,_,_,header,_,_⟩ :=
    HierarchicalRoot.root_fields _ _ _ bound.2.2.1
  have valid : request.provider.interface.valid = true := by
    rw [← header]
    exact headers.1 request.circuit.provider d foundD
  have boundary := facts.2.1
  simp only [QpeRoot.boundary,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at boundary
  simp only [Interface.valid,Bool.and_eq_true] at valid
  have input : width request.provider.interface.inputs = request.circuit.target.size :=
    HierarchicalProvider.onePort_width _ _ valid.1 boundary.1.2
  exact ⟨unitary.1.1.trans input,unitary.1.2.1.trans input⟩

theorem checkAll_provider (leaves : Leaves Operator)
    (request : QpeRoot.Request) (packet : QpeRoot.Packet) (pending : QpeRoot.Pending)
    (accepted : QpeRoot.checkAll request packet = .ok pending)
    (implementations : ∀ leaf ∈ pending.artifact.state.requests.toList, HierarchicalFiniteUnitary.Leaf leaves leaf)
    (meanings : ∀ i ∈ pending.provider.requests, ∀ obligation,
      Root.finitePair (QpeRoot.providerArtifact request packet) request.provider packet.pairs i = some obligation →
        HierarchicalRoot.FiniteEquation leaves obligation) :
    ∃ fuel value, physical algebra leaves packet.artifact fuel request.circuit.provider = some value ∧
      logical algebra leaves (HierarchicalRoot.requested request.provider) fuel request.provider.entry = some value ∧
      UnitaryInterface request.provider.interface value := by
  have stages := QpeRoot.checkAll_conditions request packet pending accepted
  have facts := QpeRoot.assemble_conditions request packet pending.artifact pending stages.2
  exact HierarchicalProvider.inspect_unitary leaves packet.artifact packet.order pending.artifact stages.1
    request.circuit.provider packet.providerProof facts.2.2.1 request.provider packet.pairs packet.pairOrder
    _ pending.provider facts.2.2.2.1 implementations meanings

/-- An independently interpreted requested provider, including global phase,
is exactly the operator used at every controlled power in the same artifact. -/
theorem checkAll_provider_equal (leaves : Leaves Operator)
    (request : QpeRoot.Request) (packet : QpeRoot.Packet) (pending : QpeRoot.Pending)
    (accepted : QpeRoot.checkAll request packet = .ok pending)
    (implementations : ∀ leaf ∈ pending.artifact.state.requests.toList, HierarchicalFiniteUnitary.Leaf leaves leaf)
    (meanings : ∀ i ∈ pending.provider.requests, ∀ obligation,
      Root.finitePair (QpeRoot.providerArtifact request packet) request.provider packet.pairs i = some obligation →
        HierarchicalRoot.FiniteEquation leaves obligation)
    (requestedFuel : Nat) (requested : Operator)
    (required : logical algebra leaves (HierarchicalRoot.requested request.provider)
      requestedFuel request.provider.entry = some requested) :
    ∃ fuel, physical algebra leaves packet.artifact fuel request.circuit.provider = some requested ∧
      UnitaryInterface request.provider.interface requested := by
  obtain ⟨fuel,value,actual,meaning,unitary⟩ := checkAll_provider leaves request packet pending accepted implementations meanings
  have same := evaluate_unique algebra (HierarchicalFiniteEvaluation.meaning leaves (HierarchicalRoot.requested request.provider))
    fuel requestedFuel request.provider.entry value requested meaning required
  subst value
  exact ⟨fuel,actual,unitary⟩

end Qleisli.HierarchicalQpeRoot
