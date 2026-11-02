import QleisliKernel.Qirf.RuntimeOrdinarySSA
import QleisliKernel.SourceTypes.SourceRuntimeContext

/-! Ordinary source conditions and simultaneous actual branch-phi operands.
Both original source arms remain in the event, and both fixed SSA snapshots
are read before any phi destination is added. Full branch-body/history and
typed result-storage correspondence remain duties of the common traversal.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeOrdinaryPhis
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes
open RuntimeOrdinarySSA
abbrev Phi := Semantics.Observation.ClassicalPhi

structure One (left right : Table) (phi : Phi) where
  thenValue : Read left phi.thenId
  elseValue : Read right phi.elseId

def readOne (left right : Table) (phi : Phi) : WorkM (One left right phi) := do
  let thenValue ← RuntimeOrdinarySSA.read left phi.thenId
  let elseValue ← RuntimeOrdinarySSA.read right phi.elseId
  return ⟨thenValue,elseValue⟩

def readMany (left right : Table) (phis : List Phi) :
    WorkM (List ((phi : Phi) × One left right phi)) :=
  phis.mapM fun phi => do
    let checked ← readOne left right phi
    return ⟨phi,checked⟩

def One.expression {left right phi} (one : One left right phi) (condition : Expression) : Expression :=
  .choose condition one.thenValue.expression one.elseValue.expression

/-- This statement covers either actual outcome. The other arm is not used as
this history's valuation; its original body and SSA snapshot are checked on
their own complete branch continuation. -/
theorem One.sound {left right phi reference actual} (one : One left right phi)
    (condition : Expression) (choice value : Bool) (work remaining : Nat)
    (conditionComputed : Semantics.SourceOrdinary.evaluate reference condition = some (bitValue choice))
    (agrees : Agreement reference actual (if choice then left else right))
    (executed : (Raw.Instrument.lookup actual (if choice then phi.thenId else phi.elseId)).run work =
      (.ok value,remaining)) :
    Semantics.SourceOrdinary.evaluate reference (one.expression condition) = some (bitValue value) := by
  cases choice with
  | false =>
    obtain ⟨bit,present,computed⟩ := agrees phi.elseId one.elseValue.expression one.elseValue.member
    have same : bit = value := Option.some.inj
      (present.symm.trans (RuntimeOrdinarySSA.lookup_reference _ _ _ _ _ executed))
    subst value
    simp [One.expression,Semantics.SourceOrdinary.evaluate,conditionComputed,computed,bitValue]
  | true =>
    obtain ⟨bit,present,computed⟩ := agrees phi.thenId one.thenValue.expression one.thenValue.member
    have same : bit = value := Option.some.inj
      (present.symm.trans (RuntimeOrdinarySSA.lookup_reference _ _ _ _ _ executed))
    subst value
    simp [One.expression,Semantics.SourceOrdinary.evaluate,conditionComputed,computed,bitValue]

structure Bound {sources caller dependencies program block offset}
    (source : SourceRuntimeContext.ConditionalEvent sources caller)
    (actual : @RuntimeInterval.Branch dependencies program block offset)
    (before left right : Table) where
  condition : Read before actual.condition
  phis : List ((phi : Phi) × One left right phi)
  everyRaw : phis.map Sigma.fst = actual.classical
  fresh : actual.classical.all (fun phi => (lookup before phi.output).isNone) = true
  distinct : (actual.classical.map (·.output)).Nodup

def Bound.outputs {sources caller dependencies program block offset source actual before left right}
    (bound : @Bound sources caller dependencies program block offset source actual before left right) : Table :=
  before ++ bound.phis.map fun pair => (pair.1.output,pair.2.expression source.condition)

/-- The actual Raw branch supplies every phi and its operand identities. The
source event supplies its exact original condition and both original bodies.
No output is visible while either operand snapshot is being read. -/
def read {sources caller dependencies program block offset}
    (source : SourceRuntimeContext.ConditionalEvent sources caller)
    (actual : @RuntimeInterval.Branch dependencies program block offset)
    (before left right : Table) : WorkM (Bound source actual before left right) := do
  exactWork (Exact.charge (32*(before.length+left.length+right.length+actual.classical.length+1)^2))
  let condition ← RuntimeOrdinarySSA.read before actual.condition
  let phis ← readMany left right actual.classical
  if everyRaw : phis.map Sigma.fst = actual.classical then
    if fresh : actual.classical.all (fun phi => (lookup before phi.output).isNone) = true then
      if distinct : (actual.classical.map (·.output)).Nodup then
        return ⟨condition,phis,everyRaw,fresh,distinct⟩
      else throw .request
    else throw .request
  else throw .request

structure ConditionAt {sources caller dependencies program block offset source actual before left right}
    (bound : @Bound sources caller dependencies program block offset source actual before left right)
    (reference : Valuation) (values : Values) where
  value : Bool
  raw : RuntimeInterval.Computed (Raw.Instrument.lookup values actual.condition) value
  source : Semantics.SourceOrdinary.evaluate reference source.condition = some (bitValue value)

/-- Check the original source condition against the actual Raw condition under
the same full source valuation and classical history. The enclosing traversal
must call this for every active branch occurrence in every complete history. -/
def readCondition {sources caller dependencies program block offset source actual before left right}
    (bound : @Bound sources caller dependencies program block offset source actual before left right)
    (reference : Valuation) (values : Values) : WorkM (ConditionAt bound reference values) := do
  exactWork (Exact.charge (32*(SourceRuntimeValues.expressionSize source.condition+
    SourceRuntimeValues.expressionFields source.condition+values.length+1)))
  let value ← NaturalAffine.witness (Raw.Instrument.lookup values actual.condition)
  if computed : Semantics.SourceOrdinary.evaluate reference source.condition = some (bitValue value.val) then
    return ⟨value.val,by with_reducible exact value.property,computed⟩
  else throw .equation

theorem Bound.bothOperands {sources caller dependencies program block offset source actual before left right}
    (bound : @Bound sources caller dependencies program block offset source actual before left right)
    (phi : Phi) (member : phi ∈ actual.classical) : Nonempty (One left right phi) := by
  rw [← bound.everyRaw] at member
  obtain ⟨pair,_present,same⟩ := List.mem_map.mp member
  cases same
  exact ⟨pair.2⟩

end QleisliKernel.Qirf.RuntimeOrdinaryPhis
