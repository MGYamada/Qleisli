import QleisliKernel.Qirf.EngineeringPure
import Qleisli.EngineeringPure
import Qleisli.QirfValidity
import Qleisli.RawBranchFunction
import Qleisli.ExactMatrix

/-! Original-body meaning for the separate engineering-only pure comparison.
The two existing exact gates establish each body's own requested matrix and
isometry; the separate inequality relates those matrices without identifying
their meanings. No source/transport/native-compiler preservation, hardware
realization, resource bound or constitutional guarantee admission follows.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.NativeEngineeringPure
open QleisliKernel QleisliKernel.Semantics.Finite QleisliKernel.Semantics.Exact
open QleisliKernel.Qirf.EngineeringPure
open Qleisli.Semantics.ObservingFunction
open scoped BigOperators

/-- Semantic consequences of one existing PureLeaf execution. The exact
original root, dependency graph, type trees and ordered ports remain explicit. -/
structure LeafMeaning (leaf : LeafRequest) (domain codomain : Basis)
    (checked : QleisliKernel.Qirf.PureLeaf.Checked) : Prop where
  rootMeaning : Qleisli.Qirf.Validity.RootMeaning leaf.artifact leaf.order checked.root
  domainValid : QleisliKernel.Finite.basisValid domain = true
  codomainValid : QleisliKernel.Finite.basisValid codomain = true
  interface : leaf.artifact.rootInterface = some (domain,codomain)
  inputs : checked.root.program.inputs = [leaf.input]
  outputs : checked.root.program.outputs = [leaf.output.token]
  classicalInputs : checked.root.program.classicalInputs = []
  classicalOutputs : checked.root.program.classicalOutputs = []
  inputWidth : leaf.input.bits = width domain
  outputWidth : leaf.output.bits = width codomain
  live : checked.root.checked.state.quantum.live = [leaf.output]
  pureEffect : checked.root.program.effect = .unitary ∨ checked.root.program.effect = .iso
  rows : leaf.required.rows = 2^width codomain
  cols : leaf.required.cols = 2^width domain
  equation : checked.actual = leaf.required
  body : BodyMeaning checked.root.dependencies checked.root.program leaf.required
  gram : ∀ row col, row < leaf.required.cols → col < leaf.required.cols →
    ((List.range leaf.required.rows).map (fun k =>
      star (Qleisli.Semantics.Exact.entry leaf.required k row) *
        Qleisli.Semantics.Exact.entry leaf.required k col)).sum = if row = col then 1 else 0

theorem leaf_meaning (leaf : LeafRequest) (domain codomain : Basis)
    (checked : QleisliKernel.Qirf.PureLeaf.Checked) (work left : Nat)
    (ok : (QleisliKernel.Qirf.PureLeaf.check leaf.artifact leaf.order domain codomain
      leaf.input leaf.output leaf.required).run work = (.ok checked,left)) :
    LeafMeaning leaf domain codomain checked := by
  have facts := QleisliKernel.Qirf.PureLeaf.check_postcondition _ _ _ _ _ _ _ _ _ _ ok
  obtain ⟨after,accepted⟩ := facts.root
  have root := Qleisli.Qirf.Validity.root_meaning _ _ _ _
    (QleisliKernel.Qirf.Validity.checkRoot_postcondition _ _ _ _ _ accepted)
  obtain ⟨a,b,reconstructed⟩ := facts.body
  have body := Qleisli.Raw.BranchFunction.reconstruct_denotes _ _ facts.classicalInputs
    _ _ _ reconstructed
  obtain ⟨c,d,isometry⟩ := facts.isometry
  have gram := (Qleisli.Exact.isometry_gram _ _ _ isometry).2
  rw [facts.equation] at body gram
  exact {
    rootMeaning := root
    domainValid := facts.domainValid
    codomainValid := facts.codomainValid
    interface := facts.interface
    inputs := facts.inputs
    outputs := facts.outputs
    classicalInputs := facts.classicalInputs
    classicalOutputs := facts.classicalOutputs
    inputWidth := facts.inputWidth
    outputWidth := facts.outputWidth
    live := facts.live
    pureEffect := facts.pureEffect
    rows := facts.rows
    cols := facts.cols
    equation := facts.equation
    body := body
    gram := gram }

/-- Both exact original-body meanings and a phase-sensitive Euclidean operator
bound. This remains an engineering relation even when epsilon is zero; it
constructs no exact correspondence, capability, cleanup or resource handle. -/
structure Meaning (request : Request) (checked : Checked) : Prop where
  actual : LeafMeaning request.actual request.domain request.codomain checked.actual
  ideal : LeafMeaning request.ideal request.domain request.codomain checked.ideal
  bound : Qleisli.Semantics.EngineeringPure.OperatorBound
    request.actual.required request.ideal.required request.epsilon

theorem check_meaning (request : Request) (checked : Checked) (work left : Nat)
    (ok : (QleisliKernel.Qirf.EngineeringPure.check request).run work = (.ok checked,left)) :
    Meaning request checked := by
  obtain ⟨a,b,ha,hi,hb⟩ :=
    (QleisliKernel.Qirf.EngineeringPure.check_postcondition _ _ _ _ ok).execution
  have actual := leaf_meaning _ _ _ _ _ _ ha
  have ideal := leaf_meaning _ _ _ _ _ _ hi
  have bound := Qleisli.EngineeringPure.checkMatrices_bound _ _ _ _ _ _ hb
  rw [actual.equation,ideal.equation] at bound
  exact ⟨actual,ideal,bound⟩

/-- The same executed checks bound every finite joint input without assuming
separability. The reference is untouched, and its size adds no error factor.
This is a pure-operator engineering bound, not an instrument or cleanup claim. -/
theorem check_reference_square {R : Type} [Fintype R]
    (request : Request) (checked : Checked) (work left : Nat)
    (ok : (QleisliKernel.Qirf.EngineeringPure.check request).run work = (.ok checked,left))
    (joint : Fin request.actual.required.cols → R → ℂ) :
    (∑ reference, ∑ row : Fin request.actual.required.rows, Complex.normSq
      (∑ col : Fin request.actual.required.cols,
        Qleisli.Semantics.EngineeringPure.gapMatrix request.actual.required.rows
          request.actual.required.cols request.actual.required request.ideal.required row col *
            joint col reference)) ≤
      (Qleisli.Semantics.Exact.rational request.epsilon : ℝ) ^ 2 *
        ∑ reference, ∑ col : Fin request.actual.required.cols,
          Complex.normSq (joint col reference) := by
  obtain ⟨a,b,ha,hi,hb⟩ :=
    (QleisliKernel.Qirf.EngineeringPure.check_postcondition _ _ _ _ ok).execution
  have actual := leaf_meaning _ _ _ _ _ _ ha
  have ideal := leaf_meaning _ _ _ _ _ _ hi
  rw [actual.equation,ideal.equation] at hb
  exact Qleisli.EngineeringPure.checkMatrices_reference_square _ _ _ _ _ _ hb joint

end Qleisli.NativeEngineeringPure
