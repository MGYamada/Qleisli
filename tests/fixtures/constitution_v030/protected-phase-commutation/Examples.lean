import Qleisli.RawProtectedCommutation

/-! Small executable checks and a physical phase-versus-X counterexample.
These examples do not define a borrow contract or enable source reordering.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Raw.ProtectedCommutation.Examples
open QleisliKernel.Semantics.Raw QleisliKernel.Semantics.Exact
open QleisliKernel.Semantics.Finite Qleisli.Semantics.Protected

private def source (index : Nat) : ProtectedControl := ⟨⟨.source,index⟩,true⟩
private def ancillary (index : Nat) : ProtectedControl := ⟨⟨.ancilla,index⟩,true⟩
private def phaseValue (exponent : Int) : Scalar := QleisliKernel.Exact.Scalar.phase exponent

private def diagonal (values : List Scalar) : Matrix :=
  let n := values.length
  ⟨n,n,(List.range (n*n)).map fun index =>
    if index / n == index % n then values[index / n]?.getD Scalar.zero else Scalar.zero⟩

private def requireMatrix (name : String)
    (result : Except QleisliKernel.Finite.Error Matrix × Nat) (expected : Matrix) : IO Unit := do
  match result with
  | (.error error,_) => throw (IO.userError s!"FAIL: {name}: {repr error}")
  | (.ok actual,left) =>
    unless actual == expected do throw (IO.userError s!"FAIL: {name}: wrong exact matrix {repr actual}")
    IO.println s!"PASS: {name}; rows={actual.rows}; remaining_work={left}"

private def checkPair (name : String) (sourceBits dataBits ancillaBits : Nat)
    (function : List Nat) (before after : List Use) (first second : List ProtectedControl)
    (p q : Phase) (expected : Matrix) : IO Unit := do
  requireMatrix (name ++ "/original")
    ((QleisliKernel.Raw.ProtectedEvaluation.matrix sourceBits dataBits ancillaBits function
      (before ++ .phase first p :: .phase second q :: after)).run 1000000) expected
  requireMatrix (name ++ "/swapped")
    ((QleisliKernel.Raw.ProtectedEvaluation.matrix sourceBits dataBits ancillaBits function
      (before ++ .phase second q :: .phase first p :: after)).run 1000000) expected

private def rootHalf : Scalar := ⟨.integer 0,⟨1,1⟩,.integer 0,.integer 0⟩
private def negativeRootHalf : Scalar := ⟨.integer 0,⟨-1,1⟩,.integer 0,.integer 0⟩
private def productPhase : Scalar := ⟨⟨-1,1⟩,.integer 0,⟨-1,1⟩,.integer 0⟩
private def negativeProductPhase : Scalar := ⟨⟨1,1⟩,.integer 0,⟨1,1⟩,.integer 0⟩

-- Axis 0 is the source, axis 1 the target. The literal H before and X after
-- the swapped pair are retained, so the target operator is X*H.
private def contextualExpected : Matrix := ⟨4,4,
  [rootHalf,.zero,negativeRootHalf,.zero,
   .zero,productPhase,.zero,negativeProductPhase,
   rootHalf,.zero,rootHalf,.zero,
   .zero,productPhase,.zero,productPhase]⟩

#eval show IO Unit from do
  checkPair "unit-scalar-minus-times-t" 0 0 0 [0] [] [] [] [] .minusOne .eighthTurn
    (diagonal [phaseValue 5])
  checkPair "shared-source-controls-zero-target" 2 2 0 [0,0,0,0] [] []
    [source 0,source 1] [source 1] .eighthTurn .minusOne
    (diagonal [.one,.one,phaseValue 4,phaseValue 5])
  checkPair "shared-computed-ancilla-control-zero-target" 1 1 1 [0,1] [] []
    [source 0,ancillary 0] [ancillary 0] .eighthTurn .minusOne
    (diagonal [.one,phaseValue 5])
  checkPair "retained-h-prefix-x-suffix" 1 2 0 [0,0]
    [.targetGate [] 0 .h] [.targetGate [] 0 .x]
    [source 0] [source 0] .eighthTurn .minusOne contextualExpected
  let z : Step := ⟨[⟨0,true⟩],.monomial [] [0] [4]⟩
  let x : Step := ⟨[],.monomial [0] [1,0] [0,0]⟩
  -- Both unrestricted finite circuits succeed, but exact phase distinguishes
  -- their results: X*Z differs from Z*X. Neither exchange is authorized here.
  requireMatrix "phase-then-x/noncommuting" ((QleisliKernel.Finite.circuitMatrix [] ⟨[.bit],[z,x]⟩).run 1000000)
    ⟨2,2,[.zero,phaseValue 4,.one,.zero]⟩
  requireMatrix "x-then-phase/noncommuting" ((QleisliKernel.Finite.circuitMatrix [] ⟨[.bit],[x,z]⟩).run 1000000)
    ⟨2,2,[.zero,.one,phaseValue 4,.zero]⟩

private noncomputable def seed : Physical Unit :=
  fun source _ _ _ => if source = 0 then 1 else 0

/-- Removing the protected-axis restriction would allow a false swap.
The independent physical semantics includes X so that this failure is visible. -/
theorem phase_x_do_not_commute :
    physicalUse (.protectedGate ⟨.source,0⟩ .x)
        (physicalUse (.phase [source 0] .minusOne) seed) ≠
      physicalUse (.phase [source 0] .minusOne)
        (physicalUse (.protectedGate ⟨.source,0⟩ .x) seed) := by
  intro same
  have point := congrArg (fun ψ : Physical Unit => ψ 1 0 0 ()) same
  norm_num [physicalUse,gate,seed,source,QleisliKernel.Semantics.Protected.enabled,
    QleisliKernel.Semantics.Protected.value,QleisliKernel.Semantics.Finite.bit,
    QleisliKernel.Semantics.Protected.phaseExponent,Qleisli.Semantics.Finite.phase] at point

example : QleisliKernel.Raw.usesValid 1 0 0 [.protectedGate ⟨.source,0⟩ .x] = false := by decide

private noncomputable def correlated : Physical Bool :=
  fun source ancilla target reference =>
    if ancilla = 0 ∧ target = 0 ∧ source = (if reference then 1 else 0)
    then Qleisli.Semantics.Finite.halfRoot else 0

/-- The source/reference-correlated branches retain opposite phases. Coherent
control preserves basis sectors without making the state read-only. -/
theorem correlated_phase_kickback :
    run [.phase [source 0] .minusOne] correlated 0 0 0 false = Qleisli.Semantics.Finite.halfRoot ∧
    run [.phase [source 0] .minusOne] correlated 1 0 0 true = -Qleisli.Semantics.Finite.halfRoot := by
  norm_num [run,physicalUse,correlated,source,QleisliKernel.Semantics.Protected.enabled,
    QleisliKernel.Semantics.Protected.value,QleisliKernel.Semantics.Finite.bit,
    QleisliKernel.Semantics.Protected.phaseExponent,Qleisli.Semantics.Finite.phase]

#print axioms phase_x_do_not_commute
#print axioms correlated_phase_kickback

end Qleisli.Raw.ProtectedCommutation.Examples
