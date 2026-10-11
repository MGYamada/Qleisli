import Qleisli.SharedControlCommutation
import QleisliKernel.Finite

/-! Small actual finite-matrix checks for the bounded shared-control law.
These tests do not establish a source borrow contract or a finite/hierarchy codec
correspondence. The generic hierarchy theorem is separately typechecked.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.SharedControlCommutation.Examples
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite

private def rootHalf : Scalar := ⟨.integer 0,⟨1,1⟩,.integer 0,.integer 0⟩
private def minusRootHalf : Scalar := ⟨.integer 0,⟨-1,1⟩,.integer 0,.integer 0⟩
private def minusProduct : Scalar := ⟨⟨-1,1⟩,.integer 0,⟨-1,1⟩,.integer 0⟩
private def product : Scalar := ⟨⟨1,1⟩,.integer 0,⟨1,1⟩,.integer 0⟩
private def phaseValue (n : Int) : Scalar := QleisliKernel.Exact.Scalar.phase n
private def entries (n : Nat) (value : Nat → Nat → Scalar) : Matrix :=
  ⟨n,n,(List.range (n*n)).map fun i => value (i/n) (i%n)⟩
private def identityEntry (row col : Nat) : Scalar := if row == col then .one else .zero
private def control : List Control := [⟨0,true⟩]
private def cx (axis : Nat) : Step := ⟨control,.monomial [axis] [1,0] [0,0]⟩
private def ch (axis : Nat) : Step := ⟨control,.hadamard axis⟩
private def ct (axis : Nat) : Step := ⟨control,.monomial [axis] [0,1] [0,1]⟩
private def cz (axis : Nat) : Step := ⟨control,.monomial [axis] [0,1] [0,4]⟩
private def scalarPhase (n : Nat) : Step := ⟨control,.monomial [] [0] [n]⟩

private def sharedHX : Matrix := entries 8 fun row col =>
  if row % 2 != col % 2 then .zero
  else if col % 2 == 0 then identityEntry row col
  else if row / 4 % 2 == 1-col / 4 % 2 then
    if row / 2 % 2 == 1 && col / 2 % 2 == 1 then minusRootHalf else rootHalf
  else .zero
private def sharedXT : Matrix := entries 8 fun row col =>
  if col % 2 == 0 then identityEntry row col
  else if row == col ^^^ 2 then
    if col / 4 % 2 == 1 then phaseValue 1 else .one
  else .zero
private def unitMinusH : Matrix := entries 4 fun row col =>
  if row % 2 != col % 2 then .zero
  else if col % 2 == 0 then identityEntry row col
  else if row / 2 == 1 && col / 2 == 1 then rootHalf else minusRootHalf
private def targetTUnitMinus : Matrix := entries 4 fun row col =>
  if row != col then .zero
  else if col % 2 == 0 then .one
  else if col / 2 == 0 then phaseValue 4 else phaseValue 5
private def bothUnitPhases : Matrix := ⟨2,2,[.one,.zero,.zero,phaseValue 5]⟩
private def phasesInContext : Matrix := ⟨2,2,[minusProduct,product,rootHalf,rootHalf]⟩

private def requireMatrix (name : String) (basis : Basis) (steps : List Step)
    (expected : Matrix) : IO Unit := do
  match (QleisliKernel.Finite.circuitMatrix [] ⟨basis,steps⟩).run 1000000 with
  | (.error error,_) => throw (IO.userError s!"FAIL: {name}: {repr error}")
  | (.ok actual,left) =>
    unless actual == expected do throw (IO.userError s!"FAIL: {name}: wrong exact matrix {repr actual}")
    IO.println s!"PASS: {name}; rows={actual.rows}; remaining_work={left}"
private def pair (name : String) (basis : Basis) (first second : Step)
    (expected : Matrix) (before after : List Step := []) : IO Unit := do
  requireMatrix (name ++ "/first-then-second") basis (before ++ first :: second :: after) expected
  requireMatrix (name ++ "/second-then-first") basis (before ++ second :: first :: after) expected

#eval show IO Unit from do
  -- Axis order is C,A,B, with C at the least-significant position.
  pair "shared-control-H-A-X-B" [.tuple 3,.bit,.bit,.bit] (ch 1) (cx 2) sharedHX
  pair "asymmetric-X-A-T-B" [.tuple 3,.bit,.bit,.bit] (cx 1) (ct 2) sharedXT
  pair "left-Unit-minus-right-H" [.tuple 3,.bit,.unit,.bit] (scalarPhase 4) (ch 1) unitMinusH
  pair "left-T-right-Unit-minus" [.tuple 3,.bit,.bit,.unit] (ct 1) (scalarPhase 4) targetTUnitMinus
  pair "both-Unit-scalars" [.tuple 3,.bit,.unit,.unit] (scalarPhase 4) (scalarPhase 1) bothUnitPhases
  pair "retained-H-C-prefix-X-C-suffix" [.tuple 3,.bit,.unit,.unit]
    (scalarPhase 4) (scalarPhase 1) phasesInContext
    [⟨[],.hadamard 0⟩] [⟨[],.monomial [0] [1,0] [0,0]⟩]
  -- Negative: both operations have the same mutable target.
  requireMatrix "shared-target-X-then-Z" [.pair,.bit,.bit] [cx 1,cz 1]
    ⟨4,4,[.one,.zero,.zero,.zero, .zero,.zero,.zero,.one,
      .zero,.zero,.one,.zero, .zero,phaseValue 4,.zero,.zero]⟩
  requireMatrix "shared-target-Z-then-X" [.pair,.bit,.bit] [cz 1,cx 1]
    ⟨4,4,[.one,.zero,.zero,.zero, .zero,.zero,.zero,phaseValue 4,
      .zero,.zero,.one,.zero, .zero,.one,.zero,.zero]⟩
  -- Negative: H changes the common control basis, violating the block premise.
  requireMatrix "H-control-then-CX" [.pair,.bit,.bit] [⟨[],.hadamard 0⟩,cx 1]
    ⟨4,4,[rootHalf,rootHalf,.zero,.zero, .zero,.zero,rootHalf,minusRootHalf,
      .zero,.zero,rootHalf,rootHalf, rootHalf,minusRootHalf,.zero,.zero]⟩
  requireMatrix "CX-then-H-control" [.pair,.bit,.bit] [cx 1,⟨[],.hadamard 0⟩]
    ⟨4,4,[rootHalf,.zero,.zero,rootHalf, rootHalf,.zero,.zero,minusRootHalf,
      .zero,rootHalf,rootHalf,.zero, .zero,minusRootHalf,rootHalf,.zero]⟩

-- The two columns are reference labels R=0,1, not extra physical wires.
-- The unnormalized joint seed is |C0,A0,B0,R0> + i |C1,A0,B0,R1>.
-- Both orders retain its cross-sector phase and correlation, giving
-- |000,R0> + (i/sqrt(2)) |101,R1> + (i/sqrt(2)) |111,R1> (C,A,B order).
private def correlatedSeed : Matrix := ⟨8,2,
  [.one,.zero, .zero,phaseValue 2, .zero,.zero, .zero,.zero,
   .zero,.zero, .zero,.zero, .zero,.zero, .zero,.zero]⟩
private def imaginaryRootHalf : Scalar := ⟨.integer 0,.integer 0,.integer 0,⟨1,1⟩⟩
private def correlatedExpected : Matrix := ⟨8,2,
  [.one,.zero, .zero,.zero, .zero,.zero, .zero,.zero,
   .zero,.zero, .zero,imaginaryRootHalf, .zero,.zero, .zero,imaginaryRootHalf]⟩
private def requireCorrelation (name : String) (steps : List Step) : IO Unit := do
  match (QleisliKernel.Finite.circuitMatrix [] ⟨[.tuple 3,.bit,.bit,.bit],steps⟩).run 1000000 with
  | (.error error,_) => throw (IO.userError s!"FAIL: {name}: {repr error}")
  | (.ok matrix,_) =>
    match QleisliKernel.Exact.Matrix.compose matrix correlatedSeed 1000000 with
    | (.error error,_) => throw (IO.userError s!"FAIL: {name}: {repr error}")
    | (.ok actual,_) =>
      unless actual == correlatedExpected do
        throw (IO.userError s!"FAIL: {name}: wrong joint amplitude {repr actual}")
      IO.println s!"PASS: {name}; physical_rows=8; reference_columns=2"

#eval show IO Unit from do
  requireCorrelation "correlated-reference-H-A-X-B" [ch 1,cx 2]
  requireCorrelation "correlated-reference-X-B-H-A" [cx 2,ch 1]

open Qleisli.HierarchicalOperators QleisliKernel.Hierarchical.Artifact

-- Distinct owner numbers remain in these literal interface records. Width zero
-- does not provide or discharge a source ownership/borrow proof.
private def unitTargets : Interface :=
  let side : Side := ⟨#[⟨1,#[.unit],#[]⟩,⟨2,#[.bit],#[0]⟩],#[]⟩
  ⟨side,side⟩
private def unitJoint : Interface :=
  let side : Side := ⟨#[⟨0,#[.bit],#[0]⟩,⟨1,#[.unit],#[]⟩,⟨2,#[.bit],#[1]⟩],#[]⟩
  ⟨side,side⟩
private noncomputable def scalarMinus : Operator := bounded 0 0 (fun _ _ => -1)

/-- Directly reduce the real tensor/control operator: a zero-width factor's
minus sign remains observable under the first control coordinate. -/
theorem unit_phase_visible :
    (apply unitJoint (.control true) [apply unitTargets .tensor [scalarMinus,identity 1]]).coefficient
      [true,false] [true,false] = -1 ∧
    (apply unitJoint (.control true) [apply unitTargets .tensor [scalarMinus,identity 1]]).coefficient
      [false,false] [false,false] = 1 := by
  norm_num [apply,bounded,raw,unitTargets,unitJoint,scalarMinus,identity,
    Qleisli.HierarchicalOperators.width,wires]

-- Four coherent control sectors exercise the general finite-B theorem.
-- This is an abstract four-sector algebra example, not an assertion
-- that the single-control IR constructor implements an arbitrary control type.
private noncomputable def sectorU (sector : Fin 4) :
    Matrix (Qleisli.CoordinateOperators.Bits 0) (Qleisli.CoordinateOperators.Bits 0) ℂ :=
  fun _ _ => if sector.val % 2 = 1 then -1 else 1
private noncomputable def sectorV (sector : Fin 4) :
    Matrix (Qleisli.CoordinateOperators.Bits 0) (Qleisli.CoordinateOperators.Bits 0) ℂ :=
  fun _ _ => if sector.val / 2 = 1 then Complex.I else 1
private def emptyBits : Qleisli.CoordinateOperators.Bits 0 := Fin.elim0

/-- All four phase sectors are retained, including the imaginary phases. -/
theorem four_control_sectors :
    let left := Qleisli.ControlledPowers.block (fun b => Qleisli.CoordinateOperators.tensor (sectorU b)
      (1 : Matrix (Qleisli.CoordinateOperators.Bits 0) (Qleisli.CoordinateOperators.Bits 0) ℂ))
    let right := Qleisli.ControlledPowers.block (fun b => Qleisli.CoordinateOperators.tensor
      (1 : Matrix (Qleisli.CoordinateOperators.Bits 0) (Qleisli.CoordinateOperators.Bits 0) ℂ) (sectorV b))
    (left * right) (0,emptyBits) (0,emptyBits) = 1 ∧
      (left * right) (1,emptyBits) (1,emptyBits) = -1 ∧
      (left * right) (2,emptyBits) (2,emptyBits) = Complex.I ∧
      (left * right) (3,emptyBits) (3,emptyBits) = -Complex.I := by
  dsimp only
  simp only [← Qleisli.ControlledPowers.block_mul,Qleisli.CoordinateOperators.tensor_mul,
    Matrix.mul_one,Matrix.one_mul]
  norm_num [Qleisli.ControlledPowers.block,Qleisli.CoordinateOperators.tensor,sectorU,sectorV]

theorem four_sectors_commute :
    Qleisli.ControlledPowers.block (fun b => Qleisli.CoordinateOperators.tensor (sectorU b)
      (1 : Matrix (Qleisli.CoordinateOperators.Bits 0) (Qleisli.CoordinateOperators.Bits 0) ℂ)) *
      Qleisli.ControlledPowers.block (fun b => Qleisli.CoordinateOperators.tensor
        (1 : Matrix (Qleisli.CoordinateOperators.Bits 0) (Qleisli.CoordinateOperators.Bits 0) ℂ) (sectorV b)) =
    Qleisli.ControlledPowers.block (fun b => Qleisli.CoordinateOperators.tensor
      (1 : Matrix (Qleisli.CoordinateOperators.Bits 0) (Qleisli.CoordinateOperators.Bits 0) ℂ) (sectorV b)) *
      Qleisli.ControlledPowers.block (fun b => Qleisli.CoordinateOperators.tensor (sectorU b)
        (1 : Matrix (Qleisli.CoordinateOperators.Bits 0) (Qleisli.CoordinateOperators.Bits 0) ℂ)) :=
  block_tensor_commute 0 0 sectorU sectorV

#print axioms unit_phase_visible
#print axioms four_control_sectors
#print axioms four_sectors_commute

end Qleisli.SharedControlCommutation.Examples
