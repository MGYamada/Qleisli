import QleisliKernel.Raw.Coefficient
import QleisliKernel.Raw.BranchFunction

/-! Matrix-free complete original instrument checking. All coefficients and
all hidden histories are exact; the complete Gram sum is checked entry by entry.
There is no global six-bit cap or global dense matrix. Work remains exponential
and budgeted; this is not scalable hierarchy or production integration.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw.StreamedInstrument
open Semantics.Exact Semantics.Finite Semantics.Observation Finite

structure History where
  values : Instrument.Values
  hidden : List Nat
  operator : Nat → Nat → WorkM Scalar

def initial (values : Instrument.Values) : History :=
  ⟨values,[],fun row col => pure (if row == col then Scalar.one else Scalar.zero)⟩

def merge (choice : Bool) (phis : List ClassicalPhi) (history : History) : WorkM History := do
  let values ← phis.mapM fun phi => do
    pure (phi.output,← Instrument.lookup history.values (if choice then phi.thenId else phi.elseId))
  return {history with values := history.values ++ values}

def step (dependencies : List Dependency) (recurse : List Event → History → WorkM (List History))
    (event : Event) (history : History) : WorkM (List History) := do
  exactWork (Exact.charge 1)
  match event with
  | .pure op => pure [{history with operator := (fun row col =>
        Coefficient.event dependencies op (fun row => history.operator row col) row)}]
  | .erase bits axes output => do
    guard (axesValid bits axes && (output.isNone || axes.length == 1))
    exactWork (Exact.charge (2^axes.length))
    pure ((List.range (2^axes.length)).map fun outcome =>
      ⟨Instrument.recordValue history.values output outcome,history.hidden ++ [outcome],
        fun row col => Coefficient.erased bits axes outcome (fun row => history.operator row col) row⟩)
  | .classical expr output => do
    let value ← Instrument.expression history.values expr
    pure [{history with values := history.values ++ [(output,value)]}]
  | .branch condition left right phis => do
    let choice ← Instrument.lookup history.values condition
    let next ← recurse (if choice then left else right) history
    next.mapM (merge choice phis)

def run (dependencies : List Dependency) (fuel : Nat) : List Event → History → WorkM (List History) :=
  Nat.rec (fun _ _ => throw .limit) (fun _ recurse events history =>
    events.foldlM (fun histories event => do
      let next ← histories.mapM (step dependencies recurse event)
      return next.flatten) [history]) fuel

def inner (dimension : Nat) (history : History) (row col : Nat) : WorkM Scalar :=
  Coefficient.sum dimension fun output => do
    let left ← history.operator output row
    let right ← history.operator output col
    let conjugate ← lift (arithmetic (Exact.Scalar.conjugate left))
    ProtectedEvaluation.multiply conjugate right

def gramEntry (dimension : Nat) (histories : List History) (row col : Nat) : WorkM Scalar :=
  histories.foldlM (fun previous history => do
    let value ← inner dimension history row col
    lift (arithmetic (Exact.Scalar.add previous value))) Scalar.zero

def complete (inputDimension outputDimension : Nat) (histories : List History) : WorkM Unit := do
  exactWork (Exact.charge (inputDimension*inputDimension))
  (List.range inputDimension).foldlM (fun _ row =>
    (List.range inputDimension).foldlM (fun _ col => do
      let value ← gramEntry outputDimension histories row col
      guard (value == (if row == col then Scalar.one else Scalar.zero)) .equation) ()) ()

structure Checked where
  receipts : List Semantics.ObservingFunction.Receipt
  structureCheck : Observation.Checked
  histories : List History

def inspect (inputs : List Semantics.ObservingFunction.Input) (bindings : List Semantics.ObservingFunction.Binding)
    (program : Program) (classical : List Bool) : WorkM Checked := do
  let receipts ← BranchFunction.checkAll inputs bindings
  let checked ← Observation.verify (receipts.map Semantics.ObservingFunction.Receipt.dependency) program
  guard (classical.length == program.classicalInputs.length)
  let histories ← run (receipts.map Semantics.ObservingFunction.Receipt.dependency) 65 checked.prepared.events
    (initial (program.classicalInputs.zip classical))
  guard (!histories.isEmpty)
  complete (2^checked.prepared.inputBits) (2^checked.state.quantum.frame.length) histories
  pure ⟨receipts,checked,histories⟩

theorem inspect_execution (inputs : List Semantics.ObservingFunction.Input) (bindings : List Semantics.ObservingFunction.Binding)
    (program : Program) (classical : List Bool) (checked : Checked) (work left : Nat)
    (ok : (inspect inputs bindings program classical).run work = (.ok checked,left)) :
    ∃ a b c d e f g h,
      (BranchFunction.checkAll inputs bindings).run a = (.ok checked.receipts,b) ∧
      (Observation.verify (checked.receipts.map Semantics.ObservingFunction.Receipt.dependency) program).run c =
        (.ok checked.structureCheck,d) ∧ classical.length = program.classicalInputs.length ∧
      (run (checked.receipts.map Semantics.ObservingFunction.Receipt.dependency) 65 checked.structureCheck.prepared.events
        (initial (program.classicalInputs.zip classical))).run e = (.ok checked.histories,f) ∧
      (complete (2^checked.structureCheck.prepared.inputBits)
        (2^checked.structureCheck.state.quantum.frame.length) checked.histories).run g = (.ok (),h) := by
  obtain ⟨receipts,w₁,hf,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨structureCheck,w₂,hs,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,hc,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨histories,w₄,he,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₅,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₆,hg,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst checked
  exact ⟨work,w₁,w₁,w₂,w₃,w₄,w₅,w₆,hf,hs,beq_iff_eq.mp (guard_success _ _ _ _ hc).1,he,hg⟩

end QleisliKernel.Raw.StreamedInstrument
