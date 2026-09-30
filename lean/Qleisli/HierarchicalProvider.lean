import Qleisli.HierarchicalRoot

/-! Independent meaning binding for a selected provider in one freshly checked
artifact. The fresh proof cache permits reuse without checking a second artifact
or resetting its budget. Full exact finite equations remain explicit premises.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.HierarchicalProvider
open QleisliKernel.Hierarchical
open Artifact HierarchicalFiniteEvaluation HierarchicalOperators HierarchicalTyping
open HierarchicalRoot

/-- Re-select only the entry, retaining all actual definitions, meanings,
encodings and proof objects byte for byte. -/
def atEntry (artifact : Artifact) (provider proof : Nat) : Artifact :=
  {artifact with entry := ⟨provider,proof⟩}

/-- The declared sized register fixes the number of physical axes only after
the full side header has passed validation. -/
theorem onePort_width (side : Side) (n : Nat)
    (valid : sideValid side = true)
    (one : ContractTyping.onePort side #[.bits n] = true) : width side = n := by
  cases hp : side.quantum[0]? with
  | none => simp [ContractTyping.onePort,hp] at one
  | some port =>
    have size : side.quantum.size = 1 := by
      simp [ContractTyping.onePort,hp] at one
      tauto
    have basis : port.basis = #[.bits n] := by
      simp [ContractTyping.onePort,hp] at one
      tauto
    have singleton := HierarchicalSemantics.singleton_of_get _ port size hp
    have dimensions : QleisliKernel.Layout.basisWidth port.basis.toList = some port.axes.size := by
      simp only [sideValid] at valid
      split at valid
      · contradiction
      · simp [singleton] at valid
        tauto
    rw [basis] at dimensions
    change QleisliKernel.Layout.basisWidth [.bits n] = some port.axes.size at dimensions
    rw [QleisliKernel.Layout.basisWidth_bits] at dimensions
    split at dimensions
    · have count := Option.some.inj dimensions
      simpa [width,wires,singleton] using count.symm
    · contradiction

/-- The provider's interpretation comes from its independently supplied request.
The selector must be present in the *same fresh* checker cache; a submitted proof
name, implementation name or cached success flag is not a semantic premise. -/
theorem inspect_unitary (leaves : Leaves Operator) (artifact : Artifact)
    (order : Array Nat) (pending : Conditional.Pending)
    (accepted : Conditional.checkAll artifact order = .ok pending)
    (provider proof : Nat) (present : pending.state.cache[proof]? = some true)
    (request : Root.Request) (pairs : Array Root.Pair) (pairOrder : Array Nat)
    (remaining : Nat) (binding : Root.Pending)
    (bound : Root.inspect (atEntry artifact provider proof) request pairs pairOrder remaining = .ok binding)
    (implementations : ∀ leaf ∈ pending.state.requests.toList, HierarchicalFiniteUnitary.Leaf leaves leaf)
    (meanings : ∀ i ∈ binding.requests, ∀ obligation,
      Root.finitePair (atEntry artifact provider proof) request pairs i = some obligation →
        FiniteEquation leaves obligation) :
    ∃ fuel value, physical algebra leaves artifact fuel provider = some value ∧
      logical algebra leaves (requested request) fuel request.entry = some value ∧
      UnitaryInterface request.interface value := by
  have invariant := (Conditional.checkAll_conditions artifact order pending accepted).2.2.1
  have facts := Root.inspect_conditions (atEntry artifact provider proof) request pairs pairOrder remaining binding bound
  obtain ⟨d,p,first,foundD,foundP,foundFirst,implementation,_,_,header,left,right⟩ :=
    root_fields (atEntry artifact provider proof) request pairs facts.2.2.1
  have foundP : artifact.proofs[proof]? = some p := foundP
  have implementation : p.implementation = provider := implementation
  have derived := invariant (HierarchicalFiniteUnitary.Leaf leaves) implementations proof present
  have equations := fun leaf member => HierarchicalFiniteUnitary.Leaf.equation leaves leaf (implementations leaf member)
  have derivedEquations := invariant (Equation leaves) equations proof present
  obtain ⟨fuel,value,actual,meaning⟩ := derives_evaluate algebra leaves artifact proof derivedEquations p foundP
  have unitary := HierarchicalFiniteUnitary.derives_unitary leaves artifact proof derived p foundP
  obtain ⟨parent,parentFound,parentUnitary⟩ := unitary fuel value actual
  have same : parent = d := by
    rw [implementation] at parentFound
    exact Option.some.inj (parentFound.symm.trans foundD)
  subst parent
  have matched := pairs_denote algebra leaves (atEntry artifact provider proof) request pairs
    pairOrder remaining binding bound meanings fuel 0 first foundFirst
  rw [left,right,logical_ir_only algebra leaves (atEntry artifact provider proof) artifact rfl] at matched
  exact ⟨fuel,value,by simpa only [implementation] using actual,matched ▸ meaning,header ▸ parentUnitary⟩

end Qleisli.HierarchicalProvider
