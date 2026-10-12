import Qleisli.QirfValidity
import Protocol.NativeContract

/-! Original-body semantics and exact isometry for rectangular native leaves.
These component proofs do not admit a new constitutional guarantee or establish
source/native-runtime correspondence.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.NativeContract
open QleisliKernel QleisliKernel.Protocol.NativeContract
open QleisliKernel.Semantics.Finite
open Qleisli.Semantics.ObservingFunction

structure PureLeafMeaning (artifact : QleisliKernel.Qirf.Artifact) (order : Array Nat)
    {value : Lean.Json} {work left : Nat}
    (request : PureLeafAcceptance artifact order value work left) : Prop where
  rootMeaning : Qleisli.Qirf.Validity.RootMeaning artifact order request.checked.root
  interface : artifact.rootInterface = some (request.domain,request.codomain)
  inputs : request.checked.root.program.inputs = [request.input]
  outputs : request.checked.root.program.outputs = [request.output.token]
  live : request.checked.root.checked.state.quantum.live = [request.output]
  pureEffect : request.checked.root.program.effect = .unitary ∨
    request.checked.root.program.effect = .iso
  rows : request.matrix.rows = 2^QleisliKernel.Semantics.Finite.width request.codomain
  cols : request.matrix.cols = 2^QleisliKernel.Semantics.Finite.width request.domain
  equation : request.checked.actual = request.matrix
  body : BodyMeaning request.checked.root.dependencies request.checked.root.program request.matrix
  gram : ∀ row col, row < request.matrix.cols → col < request.matrix.cols →
    ((List.range request.matrix.rows).map (fun k =>
      star (Qleisli.Semantics.Exact.entry request.matrix k row) *
        Qleisli.Semantics.Exact.entry request.matrix k col)).sum = if row = col then 1 else 0

theorem pure_leaf_meaning {artifact : QleisliKernel.Qirf.Artifact} {order : Array Nat}
    {value : Lean.Json} {work left : Nat}
    (request : PureLeafAcceptance artifact order value work left) :
    PureLeafMeaning artifact order request := by
  have facts := QleisliKernel.Qirf.PureLeaf.check_postcondition _ _ _ _ _ _ _ _ _ _ request.accepted
  obtain ⟨after,accepted⟩ := facts.root
  have root := Qleisli.Qirf.Validity.root_meaning _ _ _ _
    (QleisliKernel.Qirf.Validity.checkRoot_postcondition _ _ _ _ _ accepted)
  obtain ⟨a,b,reconstructed⟩ := facts.body
  have body := Qleisli.Raw.BranchFunction.reconstruct_denotes _ _ facts.classicalInputs _ _ _ reconstructed
  obtain ⟨c,d,isometry⟩ := facts.isometry
  have gram := (Qleisli.Exact.isometry_gram _ _ _ isometry).2
  rw [facts.equation] at body gram
  exact ⟨root,facts.interface,facts.inputs,facts.outputs,facts.live,facts.pureEffect,
    facts.rows,facts.cols,facts.equation,body,gram⟩

/-- All joint amplitudes, including entangled reference inputs, retain their
inner products. No surjectivity, executable inverse or controlled API follows. -/
theorem pure_leaf_reference {R S : Type} {artifact : QleisliKernel.Qirf.Artifact}
    {order : Array Nat} {value : Lean.Json} {work left : Nat}
    (request : PureLeafAcceptance artifact order value work left)
    (joint : Nat → R → ℂ) (other : Nat → S → ℂ) (reference : R) (otherReference : S) :
    ((List.range request.matrix.rows).map (fun row =>
      star (Qleisli.Semantics.Exact.action request.matrix joint row reference) *
        Qleisli.Semantics.Exact.action request.matrix other row otherReference)).sum =
    ((List.range request.matrix.cols).map (fun col =>
      star (joint col reference) * other col otherReference)).sum := by
  have facts := QleisliKernel.Qirf.PureLeaf.check_postcondition _ _ _ _ _ _ _ _ _ _ request.accepted
  obtain ⟨a,b,isometry⟩ := facts.isometry
  rw [facts.equation] at isometry
  exact Qleisli.Exact.isometry_inner_product _ _ _ isometry joint other reference otherReference

end Qleisli.NativeContract
