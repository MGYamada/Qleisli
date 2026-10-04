import QleisliKernel.Qirf.Validity

/-! Native encoded-contract binding reuses the existing raw, finite and exact
checkers. No host matrix is substituted for reconstruction of the actual root.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf
open Semantics.Exact Semantics.Finite Finite

def contractCircuit (signature : Basis) : Circuit :=
  ⟨signature,[⟨[],.contract (List.range (width signature)) 0 false⟩]⟩

def checkContract (artifact : Artifact) (order : Array Nat) (required : Contract) : WorkM Unit := do
  let root ← Validity.checkRoot artifact order
  let signature := required.input.physical
  guard (artifact.rootInterface == some (signature,signature)) .request
  guard (Raw.BranchFunction.preflight signature root.program) .limit
  let actual ← Raw.BranchFunction.reconstruct root.dependencies root.program
  wholeSpace actual
  let _ ← Finite.check [⟨signature,actual⟩] (contractCircuit signature) required required
  pure ()

/-- The executable entry freshly validates the complete graph, reconstructs its
original root, and discharges the caller's encoded equation with the same finite
checker. This is a composed acceptance fact, not full source/runtime Soundness. -/
theorem checkContract_bound (artifact : Artifact) (order : Array Nat)
    (required : Contract) (work left : Nat)
    (ok : (checkContract artifact order required).run work = (.ok (),left)) :
    ∃ root actual a b c d e f,
      (Validity.checkRoot artifact order).run work = (.ok root,a) ∧
      (Raw.BranchFunction.reconstruct root.dependencies root.program).run b = (.ok actual,c) ∧
      (wholeSpace actual).run c = (.ok (),d) ∧
      (Finite.check [⟨required.input.physical,actual⟩]
        (contractCircuit required.input.physical) required required).run d = (.ok e,f) := by
  obtain ⟨root,a,hr,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,b,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨actual,c,ha,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,d,hu,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨result,f,he,_⟩ := bind_success _ _ _ _ _ h
  exact ⟨root,actual,a,b,c,d,result,f,hr,ha,hu,he⟩

/-- The exact interface, closed-body preflight and continuous work states of
the existing encoded checker. No wrapper/operator equality is assumed here. -/
theorem checkContract_conditions (artifact : Artifact) (order : Array Nat)
    (required : Contract) (work left : Nat)
    (ok : (checkContract artifact order required).run work = (.ok (),left)) :
    ∃ root actual wrapper a b c,
      (Validity.checkRoot artifact order).run work = (.ok root,a) ∧
      artifact.rootInterface = some (required.input.physical,required.input.physical) ∧
      Raw.BranchFunction.preflight required.input.physical root.program = true ∧
      (Raw.BranchFunction.reconstruct root.dependencies root.program).run a = (.ok actual,b) ∧
      (wholeSpace actual).run b = (.ok (),c) ∧
      (Finite.check [⟨required.input.physical,actual⟩]
        (contractCircuit required.input.physical) required required).run c = (.ok wrapper,left) := by
  obtain ⟨root,a,hr,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,a₁,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨interface,same₁⟩ := guard_success _ _ _ _ hi
  subst a₁
  obtain ⟨_,a₂,hp,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨preflight,same₂⟩ := guard_success _ _ _ _ hp
  subst a₂
  obtain ⟨actual,b,ha,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,c,hu,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨wrapper,d,hw,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).2
  subst d
  exact ⟨root,actual,wrapper,a,b,c,hr,beq_iff_eq.mp interface,preflight,ha,hu,hw⟩

end QleisliKernel.Qirf
