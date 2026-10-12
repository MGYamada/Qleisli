import QleisliKernel.Qirf.Validity

/-! Exact rectangular equations over the original, independently checked root.
The caller supplies a requirement, never a reconstructed action or a receipt.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.PureLeaf
open Semantics.Exact Semantics.Finite Finite

structure Checked where
  root : Validity.Root
  actual : Matrix

/-- Both source type trees and both ordered owner ports are part of the
obligation. This grants neither a two-sided inverse nor controlled access. -/
def check (artifact : Artifact) (order : Array Nat) (domain codomain : Basis)
    (input output : Semantics.Raw.Port) (required : Matrix) : WorkM Checked := do
  let root ← Validity.checkRoot artifact order
  guard (basisValid domain && basisValid codomain) .limit
  guard (artifact.rootInterface == some (domain,codomain)) .request
  guard (root.program.inputs == [input] && root.program.outputs == [output.token] &&
    root.program.classicalInputs.isEmpty && root.program.classicalOutputs.isEmpty &&
    (root.program.effect == .unitary || root.program.effect == .iso)) .request
  guard (input.bits == width domain && output.bits == width codomain &&
    root.checked.state.quantum.live == [output]) .request
  guard (required.rows == 2^width codomain && required.cols == 2^width domain) .request
  let actual ← Raw.BranchFunction.reconstruct root.dependencies root.program
  let isometry ← exactWork (Exact.Matrix.isometryWork actual)
  guard isometry .equation
  exactWork (Exact.charge actual.entries.length)
  guard (actual == required) .equation
  return ⟨root,actual⟩

/-- Necessary facts from this execution, including the actual root validation,
body reconstruction, exact Gram check and the independent requested matrix. -/
structure Postcondition (artifact : Artifact) (order : Array Nat) (domain codomain : Basis)
    (input output : Semantics.Raw.Port) (required : Matrix) (checked : Checked)
    (work : Nat) : Prop where
  root : ∃ after, (Validity.checkRoot artifact order).run work = (.ok checked.root,after)
  domainValid : basisValid domain = true
  codomainValid : basisValid codomain = true
  interface : artifact.rootInterface = some (domain,codomain)
  inputs : checked.root.program.inputs = [input]
  outputs : checked.root.program.outputs = [output.token]
  classicalInputs : checked.root.program.classicalInputs = []
  classicalOutputs : checked.root.program.classicalOutputs = []
  pureEffect : checked.root.program.effect = .unitary ∨ checked.root.program.effect = .iso
  inputWidth : input.bits = width domain
  outputWidth : output.bits = width codomain
  live : checked.root.checked.state.quantum.live = [output]
  rows : required.rows = 2^width codomain
  cols : required.cols = 2^width domain
  body : ∃ a b, (Raw.BranchFunction.reconstruct checked.root.dependencies checked.root.program).run a =
    (.ok checked.actual,b)
  isometry : ∃ a b, Exact.Matrix.isometry checked.actual a = (.ok true,b)
  equation : checked.actual = required

theorem check_postcondition (artifact : Artifact) (order : Array Nat) (domain codomain : Basis)
    (input output : Semantics.Raw.Port) (required : Matrix) (checked : Checked) (work left : Nat)
    (ok : (check artifact order domain codomain input output required).run work = (.ok checked,left)) :
    Postcondition artifact order domain codomain input output required checked work := by
  obtain ⟨root,a,hr,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,b,hb,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,c,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,d,hp,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,e,hl,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,f,hd,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨actual,g,ha,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨isometry,j,hs,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,k,hg,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,l,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,m,he,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst checked
  have basis := (guard_success _ _ _ _ hb).1
  have ports := (guard_success _ _ _ _ hp).1
  have live := (guard_success _ _ _ _ hl).1
  have dims := (guard_success _ _ _ _ hd).1
  simp only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,List.isEmpty_iff] at basis ports live dims
  have iso := (guard_success _ _ _ _ hg).1
  have gram := exactWork_success _ _ _ _ hs
  rw [iso] at gram
  exact ⟨⟨a,hr⟩,basis.1,basis.2,beq_iff_eq.mp (guard_success _ _ _ _ hi).1,
    ports.1.1.1.1,ports.1.1.1.2,ports.1.1.2,ports.1.2,ports.2,
    live.1.1,live.1.2,live.2,dims.1,dims.2,⟨f,g,ha⟩,⟨g,j,gram⟩,
    beq_iff_eq.mp (guard_success _ _ _ _ he).1⟩

end QleisliKernel.Qirf.PureLeaf
