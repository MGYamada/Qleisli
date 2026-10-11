import QleisliKernel.Raw.Observation

/-! Exact finite instruments from independently read original raw programs.
Every hidden erasure outcome and unnormalized residual operator is retained.
No producer matrix, Rust acceptance flag or classical probability is trusted.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw.Instrument
open Semantics.Exact Semantics.Finite Semantics.Observation Finite

abbrev Values := List (Nat × Bool)

structure History where
  values : Values
  hidden : List Nat
  operator : Matrix
  deriving Repr

def lookup (values : Values) (id : Nat) : WorkM Bool :=
  lift (readOption ((values.find? (fun pair => pair.1 == id)).map (·.2)))

def expression (values : Values) : Expr → WorkM Bool
  | .constant value => pure value
  | .not input => do return !(← lookup values input)
  | .xor left right => do return (← lookup values left) != (← lookup values right)
  | .and left right => do return (← lookup values left) && (← lookup values right)

def recordValue (values : Values) (output : Option Nat) (outcome : Nat) : Values :=
  match output with
  | none => values
  | some id => values ++ [(id,outcome == 1)]

def erase (bits : Nat) (axes : List Nat) (outcome : Nat) : WorkM Matrix := do
  guard (bits ≤ 6) .limit
  guard (axesValid bits axes && outcome < 2^axes.length)
  let kept := (List.range bits).filter (fun axis => !axes.contains axis)
  let rows := 2^kept.length
  let cols := 2^bits
  exactWork (Exact.charge (rows*cols))
  lift (arithmetic (Exact.Matrix.make rows cols ((List.range (rows*cols)).map fun index =>
    if gather (index % cols) axes == outcome && gather (index % cols) kept == index / cols
    then Scalar.one else Scalar.zero)))

def apply (history : History) (operator : Matrix) : WorkM History := do
  let actual ← exactWork (Exact.Matrix.composeWork operator history.operator)
  return {history with operator := actual}

/-- Phi operands are read simultaneously from the selected arm snapshot, so
an earlier phi output can never become a later phi's input. -/
def mergeClassical (choice : Bool) (phis : List ClassicalPhi) (history : History) : WorkM History := do
  let values ← phis.mapM fun phi => do
    let value ← lookup history.values (if choice then phi.thenId else phi.elseId)
    pure (phi.output,value)
  return {history with values := history.values ++ values}

def stepEvent (dependencies : List Dependency)
    (recurse : List Event → History → WorkM (List History))
    (event : Event) (history : History) : WorkM (List History) := do
        exactWork (Exact.charge 1)
        match event with
        | .pure operation => do
          let operator ← Raw.ProtectedEvaluation.eventMatrix dependencies operation
          return [← apply history operator]
        | .erase bits axes output => do
          guard (bits ≤ 6) .limit
          guard (output.isNone || axes.length == 1)
          (List.range (2^axes.length)).mapM fun outcome => do
            let operator ← erase bits axes outcome
            let next ← apply history operator
            let values := recordValue history.values output outcome
            return {next with values,hidden := history.hidden ++ [outcome]}
        | .classical expr output => do
          let value ← expression history.values expr
          return [{history with values := history.values ++ [(output,value)]}]
        | .branch condition thenEvents elseEvents phis => do
          let choice ← lookup history.values condition
          let next ← recurse (if choice then thenEvents else elseEvents) history
          next.mapM (mergeClassical choice phis)

def runEvents (dependencies : List Dependency) (fuel : Nat) : List Event → History → WorkM (List History) :=
  Nat.rec (fun _ _ => throw .limit) (fun _ recurse events initial =>
    events.foldlM (fun histories event => do
      let next ← histories.mapM (stepEvent dependencies recurse event)
      return next.flatten) [initial]) fuel

/-- Sum Gram matrices without imposing a global history-by-output matrix size.
Every entry is canonical exact arithmetic, charged before traversal. -/
def add (left right : Matrix) : WorkM Matrix := do
  guard (left.rows == right.rows && left.cols == right.cols)
  exactWork (Exact.charge (left.rows*left.cols))
  let entries ← (List.range (left.rows*left.cols)).mapM fun index =>
    lift (arithmetic (Exact.Scalar.add (left.entry (index / left.cols) (index % left.cols))
      (right.entry (index / left.cols) (index % left.cols))))
  lift (arithmetic (Exact.Matrix.make left.rows left.cols entries))

def addGram (sum : Matrix) (history : History) : WorkM Matrix := do
  let adjoint ← exactWork (Exact.Matrix.adjointWork history.operator)
  let gram ← exactWork (Exact.Matrix.composeWork adjoint history.operator)
  add sum gram

def gram (inputBits : Nat) (histories : List History) : WorkM Matrix := do
  let dimension := 2^inputBits
  guard (inputBits ≤ 6) .limit
  let zero ← lift (arithmetic (Exact.Matrix.make dimension dimension
    (List.replicate (dimension*dimension) Scalar.zero)))
  histories.foldlM addGram zero

structure Checked where
  structureCheck : Observation.Checked
  histories : List History

/-- Reconstruct an original body using the dependency snapshot freshly checked
by its enclosing graph. This function issues no independent dependency receipt.
Dense evaluation retains its six-bit bound and complete Kraus/Gram checking. -/
def reconstruct (dependencies : List Dependency)
    (program : Semantics.Observation.Program) (classical : List Bool) : WorkM Checked := do
  let checked ← Observation.verify dependencies program
  guard (classical.length == program.classicalInputs.length)
  guard (checked.prepared.inputBits ≤ 6 && checked.state.quantum.frame.length ≤ 6) .limit
  let initial ← lift (arithmetic (Exact.Matrix.identity (2^checked.prepared.inputBits)))
  let histories ← runEvents dependencies 65 checked.prepared.events
    ⟨program.classicalInputs.zip classical,[],initial⟩
  guard (!histories.isEmpty && histories.all fun h =>
    h.operator.rows == 2^checked.state.quantum.frame.length && h.operator.cols == 2^checked.prepared.inputBits)
  let total ← gram checked.prepared.inputBits histories
  let identity ← lift (arithmetic (Exact.Matrix.identity (2^checked.prepared.inputBits)))
  guard (total == identity) .equation
  return ⟨checked,histories⟩

/-- Ordinary checking fixes classical inputs and freshly reconstructs all
dependencies before reading the original complete instrument. QIRF callers use
the same reconstruction after checking their own original indexed graph. -/
def inspect (inputs : List Semantics.Function.Input) (bindings : List Semantics.Function.Binding)
    (program : Semantics.Observation.Program) (classical : List Bool) : WorkM Checked := do
  let receipts ← Raw.Function.checkAll inputs bindings
  reconstruct (receipts.map Semantics.Function.Receipt.dependency) program classical

/-- Factoring reconstruction preserves the entire previous WorkM recipe,
including every failure and remaining-work value, by definitional equality. -/
theorem inspect_recipe (inputs : List Semantics.Function.Input) (bindings : List Semantics.Function.Binding)
    (program : Semantics.Observation.Program) (classical : List Bool) :
    inspect inputs bindings program classical = (do
      let receipts ← Raw.Function.checkAll inputs bindings
      let dependencies := receipts.map Semantics.Function.Receipt.dependency
      let checked ← Observation.verify dependencies program
      guard (classical.length == program.classicalInputs.length)
      guard (checked.prepared.inputBits ≤ 6 && checked.state.quantum.frame.length ≤ 6) .limit
      let initial ← lift (arithmetic (Exact.Matrix.identity (2^checked.prepared.inputBits)))
      let histories ← runEvents dependencies 65 checked.prepared.events
        ⟨program.classicalInputs.zip classical,[],initial⟩
      guard (!histories.isEmpty && histories.all fun h =>
        h.operator.rows == 2^checked.state.quantum.frame.length && h.operator.cols == 2^checked.prepared.inputBits)
      let total ← gram checked.prepared.inputBits histories
      let identity ← lift (arithmetic (Exact.Matrix.identity (2^checked.prepared.inputBits)))
      guard (total == identity) .equation
      return ⟨checked,histories⟩) := rfl

theorem reconstruct_execution (dependencies : List Dependency)
    (program : Semantics.Observation.Program) (classical : List Bool)
    (checked : Checked) (work left : Nat)
    (ok : (reconstruct dependencies program classical).run work = (.ok checked,left)) :
    ∃ initial afterVerification beforeEvents afterEvents,
      (Observation.verify dependencies program).run work = (.ok checked.structureCheck,afterVerification) ∧
      Exact.Matrix.identity (2^checked.structureCheck.prepared.inputBits) = .ok initial ∧
      (runEvents dependencies 65 checked.structureCheck.prepared.events
        ⟨program.classicalInputs.zip classical,[],initial⟩).run beforeEvents = (.ok checked.histories,afterEvents) ∧
      checked.histories.all (fun h => h.operator.rows == 2^checked.structureCheck.state.quantum.frame.length &&
        h.operator.cols == 2^checked.structureCheck.prepared.inputBits) = true := by
  obtain ⟨structureCheck,w₁,hs,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨initial,w₂,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨histories,w₃,he,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,hg,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst checked
  have shape := (guard_success _ _ _ _ hg).1
  simp only [Bool.and_eq_true] at shape
  exact ⟨initial,w₁,w₂,w₃,hs,arithmetic_success _ _ (lift_success _ _ _ _ hi).1,he,shape.2⟩

theorem reconstruct_conditions (dependencies : List Dependency)
    (program : Semantics.Observation.Program) (classical : List Bool)
    (checked : Checked) (work left : Nat)
    (ok : (reconstruct dependencies program classical).run work = (.ok checked,left)) :
    ∃ afterVerification beforeGram afterGram total identity,
      (Observation.verify dependencies program).run work = (.ok checked.structureCheck,afterVerification) ∧
      (gram checked.structureCheck.prepared.inputBits checked.histories).run beforeGram = (.ok total,afterGram) ∧
      Exact.Matrix.identity (2^checked.structureCheck.prepared.inputBits) = .ok identity ∧ total = identity := by
  obtain ⟨structureCheck,w₁,hs,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨histories,w₂,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨total,w₄,hg,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨identity,_,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,he,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst checked
  exact ⟨w₁,w₃,w₄,total,identity,hs,hg,
    arithmetic_success _ _ (lift_success _ _ _ _ hi).1,beq_iff_eq.mp (guard_success _ _ _ _ he).1⟩

theorem erase_value (bits : Nat) (axes : List Nat) (outcome : Nat) (actual : Matrix)
    (work left : Nat) (ok : (erase bits axes outcome).run work = (.ok actual,left)) :
    let kept := (List.range bits).filter (fun axis => !axes.contains axis)
    actual = ⟨2^kept.length,2^bits,((List.range (2^kept.length * 2^bits)).map fun index =>
      if gather (index % 2^bits) axes == outcome && gather (index % 2^bits) kept == index / 2^bits
      then Scalar.one else Scalar.zero)⟩ := by
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  exact (Exact.matrix_make_value _ _ _ _ (arithmetic_success _ _ (lift_success _ _ _ _ h).1)).1

theorem inspect_execution (inputs : List Semantics.Function.Input) (bindings : List Semantics.Function.Binding)
    (program : Semantics.Observation.Program) (classical : List Bool) (checked : Checked) (work left : Nat)
    (ok : (inspect inputs bindings program classical).run work = (.ok checked,left)) :
    ∃ receipts initial a b c d e f,
      (Raw.Function.checkAll inputs bindings).run a = (.ok receipts,b) ∧
      (Observation.verify (receipts.map Semantics.Function.Receipt.dependency) program).run c =
        (.ok checked.structureCheck,d) ∧
      Exact.Matrix.identity (2^checked.structureCheck.prepared.inputBits) = .ok initial ∧
      (runEvents (receipts.map Semantics.Function.Receipt.dependency) 65 checked.structureCheck.prepared.events
        ⟨program.classicalInputs.zip classical,[],initial⟩).run e = (.ok checked.histories,f) ∧
      checked.histories.all (fun h => h.operator.rows == 2^checked.structureCheck.state.quantum.frame.length &&
        h.operator.cols == 2^checked.structureCheck.prepared.inputBits) = true := by
  obtain ⟨receipts,w₁,hf,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨structureCheck,w₂,hs,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨initial,w₃,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨histories,w₄,he,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,hg,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst checked
  have shape := (guard_success _ _ _ _ hg).1
  simp only [Bool.and_eq_true] at shape
  exact ⟨receipts,initial,work,w₁,w₁,w₂,w₃,w₄,hf,hs,
    arithmetic_success _ _ (lift_success _ _ _ _ hi).1,he,shape.2⟩

theorem inspect_conditions (inputs : List Semantics.Function.Input) (bindings : List Semantics.Function.Binding)
    (program : Semantics.Observation.Program) (classical : List Bool) (checked : Checked) (work left : Nat)
    (ok : (inspect inputs bindings program classical).run work = (.ok checked,left)) :
    ∃ receipts a b c d e f total identity,
      (Raw.Function.checkAll inputs bindings).run a = (.ok receipts,b) ∧
      (Observation.verify (receipts.map Semantics.Function.Receipt.dependency) program).run c =
        (.ok checked.structureCheck,d) ∧
      (gram checked.structureCheck.prepared.inputBits checked.histories).run e = (.ok total,f) ∧
      Exact.Matrix.identity (2^checked.structureCheck.prepared.inputBits) = .ok identity ∧ total = identity := by
  obtain ⟨receipts,w₁,hf,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨structureCheck,w₂,hs,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨histories,w₃,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₄,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨total,w₅,hg,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨identity,_,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,he,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst checked
  exact ⟨receipts,work,w₁,w₁,w₂,w₄,w₅,total,identity,hf,hs,hg,
    arithmetic_success _ _ (lift_success _ _ _ _ hi).1,beq_iff_eq.mp (guard_success _ _ _ _ he).1⟩

end QleisliKernel.Raw.Instrument
