import QleisliKernel.Qirf.SourceSector

/-! Small original evidence identity reductions; full source/graph/phase runtime
observations and generic composition proofs have separate retained scopes.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.Tests.SourceEntries
open QleisliKernel Semantics.Exact

def body : Semantics.Observation.Program := Semantics.Ownership.pureProgram {
  inputs := [⟨0,[],0⟩]
  operations := [.applyUnitary 0 1 [⟨[],.monomial [] [0] [2]⟩]]
  outputs := [1]
  effect := .unitary
}
def artifact (phase : Nat := 2) : Qirf.Artifact :=
  ⟨#[body],#[⟨[.unit],0,.phase8 [phase],"small::imaginary","independent::phase",[0]⟩],
    #[("small","pub unitary fn imaginary(q:Q<Unit>)->Q<Unit>{global_phase_eighth(global_phase_eighth(q))}")],0,none⟩
def identityView (entry : Qirf.Entry := ⟨[.unit],0,.phase8 [2],"small::imaginary","independent::phase",[0]⟩) :=
  ((Qirf.identity (artifact) entry).run 1000000).1.map fun identity =>
    (identity.implementation,identity.specification,identity.sources)

theorem original_entry_names_and_bytes :
    (identityView.toOption == some ("small::imaginary","independent::phase",(artifact).sources.toList)) = true :=
  by decide +kernel


theorem missing_original_source_index :
    (identityView (entry := ⟨[.unit],0,.phase8 [2],"small::imaginary","independent::phase",[1]⟩)
      matches .error .invalid) = true := by decide +kernel

theorem duplicated_original_source_index :
    (identityView (entry := ⟨[.unit],0,.phase8 [2],"small::imaginary","independent::phase",[0,0]⟩)
      matches .error .invalid) = true := by decide +kernel

theorem empty_function_identity :
    (identityView (entry := ⟨[.unit],0,.phase8 [2],"","independent::phase",[0]⟩)
      matches .error .limit) = true := by decide +kernel

end QleisliKernel.Tests.SourceEntries
