import QleisliKernel.Qirf.RuntimeInterval
import QleisliKernel.SourceTypes.SourceRuntimeOrdinary
import QleisliKernel.Semantics.OrdinaryValue
import QleisliKernel.Raw.Instrument

/-! Literal classical gaps in an original mixed runtime body.
SSA expressions are derived from actual instructions and an existing source
valuation correspondence. No producer supplies this table. Exact initial
storage, observation keys, both branch arms, simultaneous phis, complete hidden
histories and final storage remain obligations of the common body traversal.
This component allocates no quantum matrix and issues no accepted handle.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeOrdinarySSA
open QleisliKernel QleisliKernel.Finite

abbrev Expression := Semantics.SourceOrdinary.Expression
abbrev Valuation := Semantics.SourceOrdinary.Valuation
abbrev Values := Semantics.OrdinaryValue.Valuation
abbrev RawExpression := Semantics.Observation.Expr
abbrev Instruction := Semantics.Observation.Op
abbrev Table := List (Nat × Expression)

def bitValue (value : Bool) : Nat := if value then 1 else 0

def lookup (table : Table) (id : Nat) : Option Expression :=
  (table.find? (fun binding => binding.1 == id)).map (·.2)

/-- Every retained source expression agrees with the same actual classical
history. The enclosing traversal separately proves coverage of every visible
SSA identity and authenticates the source valuation's inputs/measurements. -/
def Agreement (reference : Valuation) (actual : Values) (table : Table) : Prop :=
  ∀ id expression, (id,expression) ∈ table →
    ∃ bit, Semantics.OrdinaryValue.lookup actual id = some bit ∧
      Semantics.SourceOrdinary.evaluate reference expression = some (bitValue bit)

theorem Agreement.empty (reference : Valuation) (actual : Values) :
    Agreement reference actual [] := by
  intro id expression member
  cases member

theorem Agreement.append {reference actual table} (agrees : Agreement reference actual table)
    (output : Nat) (expression : Expression) (value : Bool)
    (fresh : Semantics.OrdinaryValue.lookup actual output = none)
    (computed : Semantics.SourceOrdinary.evaluate reference expression = some (bitValue value)) :
    Agreement reference (actual ++ [(output,value)]) (table ++ [(output,expression)]) := by
  intro id source member
  rcases List.mem_append.mp member with earlier | added
  · obtain ⟨bit,present,evaluated⟩ := agrees id source earlier
    exact ⟨bit,Semantics.OrdinaryValue.append_extends actual [(output,value)] id bit present,evaluated⟩
  · have same : (id,source) = (output,expression) := List.mem_singleton.mp added
    cases same
    exact ⟨value,Semantics.OrdinaryValue.lookup_append_fresh value fresh,computed⟩

structure Read (table : Table) (id : Nat) where
  expression : Expression
  original : lookup table id = some expression
  member : (id,expression) ∈ table

private def fields (table : Table) : Nat :=
  table.foldl (fun count binding => count+1+
    SourceTypes.SourceRuntimeValues.expressionFields binding.2+
    SourceTypes.SourceRuntimeValues.expressionSize binding.2) 0

def agreement (reference : Valuation) (actual : Values) (table : Table) : Bool :=
  table.all fun (id,expression) =>
    match Semantics.OrdinaryValue.lookup actual id with
    | none => false
    | some bit => decide (Semantics.SourceOrdinary.evaluate reference expression = some (bitValue bit))

theorem agreement_sound (reference : Valuation) (actual : Values) (table : Table)
    (checked : agreement reference actual table = true) : Agreement reference actual table := by
  intro id expression member
  have one := List.all_eq_true.mp checked (id,expression) member
  change (match Semantics.OrdinaryValue.lookup actual id with
    | none => false
    | some bit => decide (Semantics.SourceOrdinary.evaluate reference expression = some (bitValue bit))) = true at one
  cases found : Semantics.OrdinaryValue.lookup actual id with
  | none => simp only [found] at one; cases one
  | some bit =>
    simp only [found] at one
    exact ⟨bit,found,of_decide_eq_true one⟩

structure CheckedAgreement (reference : Valuation) (actual : Values) (table : Table) : Type where
  original : agreement reference actual table = true
  agrees : Agreement reference actual table

/-- This finite check is repeated over the enclosing gate's complete actual
history family. It does not select histories or create a source valuation. -/
def readAgreement (reference : Valuation) (actual : Values) (table : Table) :
    WorkM (CheckedAgreement reference actual table) := do
  exactWork (Exact.charge (32*(fields table+1)*(actual.length+1)))
  if original : agreement reference actual table = true then
    return ⟨original,agreement_sound reference actual table original⟩
  else throw .equation

def read (table : Table) (id : Nat) : WorkM (Read table id) := do
  exactWork (Exact.charge (16*(fields table+1)))
  match found : table.find? (fun binding => binding.1 == id) with
  | none => throw .request
  | some (actual,expression) =>
    have same : actual = id := beq_iff_eq.mp
      (List.find?_some (p := fun binding : Nat × Expression => binding.1 == id) found)
    have member : (id,expression) ∈ table := by
      simpa only [same] using (List.mem_of_find?_eq_some found)
    return ⟨expression,by simp only [lookup,found,Option.map_some],member⟩

inductive Definition (table : Table) : RawExpression → Expression → Type where
  | constant (value : Bool) : Definition table (.constant value) (.bit value)
  | not (input : Nat) (operand : Read table input) :
      Definition table (.not input) (.not operand.expression)
  | xor (left right : Nat) (first : Read table left) (second : Read table right) :
      Definition table (.xor left right) (.xor first.expression second.expression)
  | and (left right : Nat) (first : Read table left) (second : Read table right) :
      Definition table (.and left right) (.and first.expression second.expression)

def readExpression (table : Table) (raw : RawExpression) :
    WorkM ((source : Expression) × Definition table raw source) := do
  match raw with
  | .constant value => return ⟨.bit value,.constant value⟩
  | .not input =>
    let operand ← read table input
    return ⟨.not operand.expression,.not input operand⟩
  | .xor left right =>
    let first ← read table left
    let second ← read table right
    return ⟨.xor first.expression second.expression,.xor left right first second⟩
  | .and left right =>
    let first ← read table left
    let second ← read table right
    return ⟨.and first.expression second.expression,.and left right first second⟩

theorem lookup_reference (actual : Values) (id : Nat) (value : Bool) (work left : Nat)
    (executed : (Raw.Instrument.lookup actual id).run work = (.ok value,left)) :
    Semantics.OrdinaryValue.lookup actual id = some value := by
  change (lift (readOption (Semantics.OrdinaryValue.lookup actual id))).run work =
    (.ok value,left) at executed
  have original := (lift_success _ _ _ _ executed).1
  cases found : Semantics.OrdinaryValue.lookup actual id with
  | none => simp [found,readOption] at original
  | some bit =>
    simp only [found,readOption,Except.ok.injEq] at original
    exact congrArg some original

/-- Agreement is preserved against the actual executable Instrument expression
reader for every source valuation and actual history, without probabilities. -/
theorem Definition.sound {table raw source reference actual}
    (definition : Definition table raw source) (agrees : Agreement reference actual table)
    (value : Bool) (work left : Nat)
    (executed : (Raw.Instrument.expression actual raw).run work = (.ok value,left)) :
    Semantics.SourceOrdinary.evaluate reference source = some (bitValue value) := by
  cases definition with
  | constant bit =>
    have same : value = bit := (pure_success _ _ _ _ executed).1
    subst value
    rfl
  | not input operand =>
    obtain ⟨bit,present,computed⟩ := agrees input operand.expression operand.member
    change ((Raw.Instrument.lookup actual input) >>= fun bit => pure (!bit)).run work =
      (.ok value,left) at executed
    obtain ⟨actualBit,middle,read,finish⟩ := bind_success _ _ _ _ _ executed
    have same : bit = actualBit := Option.some.inj
      (present.symm.trans (lookup_reference _ _ _ _ _ read))
    subst actualBit
    have result : value = !bit := (pure_success _ _ _ _ finish).1
    subst value
    cases bit <;> simp [Semantics.SourceOrdinary.evaluate,computed,bitValue]
  | xor leftId rightId first second =>
    obtain ⟨leftBit,leftPresent,leftComputed⟩ := agrees leftId first.expression first.member
    obtain ⟨rightBit,rightPresent,rightComputed⟩ := agrees rightId second.expression second.member
    change ((Raw.Instrument.lookup actual leftId) >>= fun left =>
      (Raw.Instrument.lookup actual rightId) >>= fun right => pure (left != right)).run work =
      (.ok value,left) at executed
    obtain ⟨actualLeft,middle,firstRead,rest⟩ := bind_success _ _ _ _ _ executed
    obtain ⟨actualRight,last,secondRead,finish⟩ := bind_success _ _ _ _ _ rest
    have leftSame : leftBit = actualLeft := Option.some.inj
      (leftPresent.symm.trans (lookup_reference _ _ _ _ _ firstRead))
    have rightSame : rightBit = actualRight := Option.some.inj
      (rightPresent.symm.trans (lookup_reference _ _ _ _ _ secondRead))
    subst actualLeft
    subst actualRight
    have result : value = (leftBit != rightBit) := (pure_success _ _ _ _ finish).1
    subst value
    cases leftBit <;> cases rightBit <;>
      simp [Semantics.SourceOrdinary.evaluate,leftComputed,rightComputed,bitValue]
  | and leftId rightId first second =>
    obtain ⟨leftBit,leftPresent,leftComputed⟩ := agrees leftId first.expression first.member
    obtain ⟨rightBit,rightPresent,rightComputed⟩ := agrees rightId second.expression second.member
    change ((Raw.Instrument.lookup actual leftId) >>= fun left =>
      (Raw.Instrument.lookup actual rightId) >>= fun right => pure (left && right)).run work =
      (.ok value,left) at executed
    obtain ⟨actualLeft,middle,firstRead,rest⟩ := bind_success _ _ _ _ _ executed
    obtain ⟨actualRight,last,secondRead,finish⟩ := bind_success _ _ _ _ _ rest
    have leftSame : leftBit = actualLeft := Option.some.inj
      (leftPresent.symm.trans (lookup_reference _ _ _ _ _ firstRead))
    have rightSame : rightBit = actualRight := Option.some.inj
      (rightPresent.symm.trans (lookup_reference _ _ _ _ _ secondRead))
    subst actualLeft
    subst actualRight
    have result : value = (leftBit && rightBit) := (pure_success _ _ _ _ finish).1
    subst value
    cases leftBit <;> cases rightBit <;>
      simp [Semantics.SourceOrdinary.evaluate,leftComputed,rightComputed,bitValue]

def instruction (raw : RawExpression) (output : Nat) : Instruction :=
  match raw with
  | .constant value => .constant value output
  | .not input => .not input output
  | .xor left right => .xor left right output
  | .and left right => .and left right output

structure Action (table : Table) (operation : Instruction) where
  raw : RawExpression
  output : Nat
  literal : operation = instruction raw output
  source : Expression
  definition : Definition table raw source
  fresh : lookup table output = none

def Action.after {table operation} (action : Action table operation) : Table :=
  table ++ [(action.output,action.source)]

private def readDefinition (table : Table) (raw : RawExpression) (output : Nat) :
    WorkM (Action table (instruction raw output)) := do
  exactWork (Exact.charge (16*(fields table+1)))
  if fresh : lookup table output = none then
    let definition ← readExpression table raw
    return ⟨raw,output,rfl,definition.1,definition.2,fresh⟩
  else throw .request

def readAction (table : Table) (operation : Instruction) : WorkM (Action table operation) :=
  match operation with
  | .constant value output => readDefinition table (.constant value) output
  | .not input output => readDefinition table (.not input) output
  | .xor left right output => readDefinition table (.xor left right) output
  | .and left right output => readDefinition table (.and left right) output
  | _ => throw .request

theorem Action.preserves {table operation reference actual} (action : Action table operation)
    (agrees : Agreement reference actual table) (value : Bool) (work left : Nat)
    (fresh : Semantics.OrdinaryValue.lookup actual action.output = none)
    (executed : (Raw.Instrument.expression actual action.raw).run work = (.ok value,left)) :
    Agreement reference (actual ++ [(action.output,value)]) action.after :=
  agrees.append action.output action.source value fresh (action.definition.sound agrees value work left executed)

inductive Sequence : Table → List Instruction → Table → Type where
  | nil (table : Table) : Sequence table [] table
  | cons {table operation operations after} (head : Action table operation)
      (tail : Sequence head.after operations after) : Sequence table (operation :: operations) after

def readOps : (operations : List Instruction) → (table : Table) →
    WorkM ((after : Table) × Sequence table operations after)
  | [],table => return ⟨table,.nil table⟩
  | operation :: operations,table => do
    let head ← readAction table operation
    let tail ← readOps operations head.after
    return ⟨tail.1,.cons head tail.2⟩

def classicalOnly : Instruction → Bool
  | .constant .. | .not .. | .xor .. | .and .. => true
  | _ => false

theorem Action.classical {table operation} (action : Action table operation) :
    classicalOnly operation = true := by
  rw [action.literal]
  cases action.raw <;> rfl

theorem Sequence.classical {table operations after} (sequence : Sequence table operations after) :
    operations.all classicalOnly = true := by
  induction sequence with
  | nil table => rfl
  | cons head tail ih => simp only [List.all_cons,head.classical,ih,Bool.true_and]

structure Gap {dependencies program} (block : RuntimeInterval.Block dependencies program)
    (start count : Nat) (before : Table) where
  interval : RuntimeInterval.Checked block start count
  after : Table
  sequence : Sequence before ((block.operations.drop start).take count) after

/-- Every operation in the exact literal gap is consumed. A branch, quantum
action or destructive event refuses; none can hide between source intervals. -/
def readGap {dependencies program} (block : RuntimeInterval.Block dependencies program)
    (start count : Nat) (before : Table) : WorkM (Gap block start count before) := do
  let interval ← RuntimeInterval.check block start count
  let compiled ← readOps ((block.operations.drop start).take count) before
  return ⟨interval,compiled.1,compiled.2⟩

theorem Gap.classical {dependencies program block start count before}
    (gap : @Gap dependencies program block start count before) :
    ((block.operations.drop start).take count).all classicalOnly = true := gap.sequence.classical

end QleisliKernel.Qirf.RuntimeOrdinarySSA
