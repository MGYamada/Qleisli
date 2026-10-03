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

end QleisliKernel.Qirf
