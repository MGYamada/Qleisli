import QleisliKernel.Qirf.RuntimeInteriorAssembly
import QleisliKernel.Qirf.RuntimeTransitiveInterior
import QleisliKernel.Qirf.RuntimeClosedSubject

/-! Follow a root operation formal across the original named call path. Each
wrapper consumes one authentic native selection and one stored substitution.
Constructed arguments retain their located interior uses at the supplying
call. The remaining transport stays attached to the checked chain.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeForwardedSupply
open QleisliKernel Finite SourceTypes GenericDutyQueue
open QleisliKernel.SourceTypes.GenericOperationSubstitute (Subject)
open RuntimeDutyInvocation (Binding Edge)
open RuntimeNativeSubject (Cursor Formal)
open RuntimeClosedSubject (Paired)
open RuntimeInterval (Computed)
open QleisliKernel.Semantics.SymbolicBasis (Parameter)

def keyOf : GenericOperation.Node → Option Parameter
  | .formal key => some key
  | _ => none

private theorem keyOf_some {node key} (found : keyOf node = some key) : node = .formal key := by
  cases node <;> simp_all [keyOf]

def wrapped : OperationDescription.Node → Bool
  | .formal .. => true
  | _ => false

structure Wrapper {artifact catalogue context description graph implementations references prepared root requested checked
    native index cursor terminal}
    (paired : @Paired artifact catalogue context description graph implementations references prepared root requested
      checked native index cursor terminal) where
  selected : Formal cursor
  selection : Computed (RuntimeNativeSubject.readFormal cursor) selected
  child : Paired checked native index selected.child.cursor terminal
  original : Paired.formal selected selection child = paired

private def unwrap {artifact catalogue context description graph implementations references prepared root requested checked
    native index cursor terminal}
    (paired : @Paired artifact catalogue context description graph implementations references prepared root requested
      checked native index cursor terminal) : Option (Wrapper paired) :=
  match paired with
  | .node .. => none
  | .formal selected selection child => some ⟨selected,selection,child,rfl⟩

structure Selected {artifact catalogue context description graph implementations references prepared root requested checked
    native index cursor terminal caller original}
    (event : SourceRuntimeContext.NamedEvent artifact.sources caller) (app : GenericOperation.ApplicationSource artifact.sources)
    (transfer : GenericOperationSubstitute.Checked app original)
    (paired : @Paired artifact catalogue context description graph implementations references prepared root requested
      checked native index cursor terminal) where
  key : Parameter
  source : original.description.nodes[original.description.root]? = some (.formal key)
  wrapper : Wrapper paired
  choice : RuntimeFormalActual.Choice
  actual : Computed (RuntimeFormalActual.readChoice wrapper.selected) choice
  supply : RuntimeFormalActual.Supply event app transfer key choice
  supplied : Computed (RuntimeFormalActual.readSupply event app transfer key choice) supply
  returned : transfer.result.subject = ⟨supply.genericActual.subject,supply.genericActual.suppliers⟩

/-- A root formal is already handled by the next named call. A concrete
argument without lexical Op nodes needs no traversal of its written syntax. -/
private def hasInterior (original : GenericOperation.Description) : Bool :=
  match original.nodes[original.root]? with
  | none | some (.formal _) => false
  | some _ => original.nodes.any fun node => (keyOf node).isSome

def AtCaller {artifact catalogue context description graph implementations references prepared root requested checked
    native index cursor terminal caller original event app transfer paired queue rootOwner rootName owner name path record invocation result}
    (hop : @Selected artifact catalogue context description graph implementations references prepared root requested checked
      native index cursor terminal caller original event app transfer paired)
    (prior : @Binding artifact.sources catalogue queue rootOwner rootName owner name path record invocation)
    (remaining : GenericDutyQueue.Transport invocation.applications.reverse transfer.result.subject result) : Type :=
  match prior,remaining with
  | .root ..,_ => Empty
  | .named (event := outer) (invocation := parent) (application := supplying) (target := target) outerPrior _,receipt =>
    let pieces := RuntimeFormalActual.splitInvocation parent supplying target receipt
    Σ immediate : {value : RuntimeInteriorSupply.Checked hop.supply outer supplying.original pieces.transfer hop.wrapper.child //
      Computed (RuntimeInteriorSupply.read hop.supply outer supplying.original pieces.transfer hop.wrapper.child) value},
      {trees : (i : Fin immediate.val.entries.length) →
        RuntimeTransitiveInterior.Tree (RuntimeTransitiveInterior.taskOf
          (RuntimeTransitiveInterior.Site.ofLeaf [] immediate.val.entries[i].leaf) outerPrior pieces.tail) //
        Computed (RuntimeTransitiveInterior.read outerPrior pieces.tail immediate.val.entries) trees}

private def readAtCaller {artifact catalogue context description graph implementations references prepared root requested checked
    native index cursor terminal caller original event app transfer paired queue rootOwner rootName owner name path record invocation result}
    (hop : @Selected artifact catalogue context description graph implementations references prepared root requested checked
      native index cursor terminal caller original event app transfer paired)
    (prior : @Binding artifact.sources catalogue queue rootOwner rootName owner name path record invocation)
    (remaining : GenericDutyQueue.Transport invocation.applications.reverse transfer.result.subject result) : WorkM (AtCaller hop prior remaining) :=
  match prior,remaining with
  | .root ..,_ => throw .request
  | .named (event := outer) (invocation := parent) (application := supplying) (target := target) outerPrior _,receipt =>
    do
      let pieces := RuntimeFormalActual.splitInvocation parent supplying target receipt
      let immediate ← NaturalAffine.witness
        (RuntimeInteriorSupply.read hop.supply outer supplying.original pieces.transfer hop.wrapper.child)
      let followed ← NaturalAffine.witness (RuntimeTransitiveInterior.read outerPrior pieces.tail immediate.val.entries)
      return ⟨⟨immediate.val,by with_reducible exact immediate.property⟩,
        ⟨followed.val,by with_reducible exact followed.property⟩⟩

inductive Interior {artifact catalogue context description graph implementations references prepared root requested checked
    native index cursor terminal caller original event app transfer paired queue rootOwner rootName owner name path record invocation result}
    (hop : @Selected artifact catalogue context description graph implementations references prepared root requested checked
      native index cursor terminal caller original event app transfer paired)
    (prior : @Binding artifact.sources catalogue queue rootOwner rootName owner name path record invocation)
    (remaining : GenericDutyQueue.Transport invocation.applications.reverse transfer.result.subject result) where
  | noInterior (none : hasInterior hop.supply.genericActual.subject = false)
  | located (needed : hasInterior hop.supply.genericActual.subject = true)
      (value : AtCaller hop prior remaining)
      (computed : Computed (readAtCaller hop prior remaining) value)

def readInterior {artifact catalogue context description graph implementations references prepared root requested checked
    native index cursor terminal caller original event app transfer paired queue rootOwner rootName owner name path record invocation result}
    (hop : @Selected artifact catalogue context description graph implementations references prepared root requested checked
      native index cursor terminal caller original event app transfer paired)
    (prior : @Binding artifact.sources catalogue queue rootOwner rootName owner name path record invocation)
    (remaining : GenericDutyQueue.Transport invocation.applications.reverse transfer.result.subject result) : WorkM (Interior hop prior remaining) := do
  exactWork (Exact.charge (16*(hop.supply.genericActual.subject.nodes.length+1)))
  match needed : hasInterior hop.supply.genericActual.subject with
  | false => return .noInterior needed
  | true =>
    let located ← NaturalAffine.witness (readAtCaller hop prior remaining)
    return .located needed located.val (by with_reducible exact located.property)

inductive Chain {artifact catalogue context description graph implementations references prepared root requested}
    {checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested}
    {queue : GenericDutyQueue.Checked catalogue} {rootOwner rootName : String} {native : OperationDescription.Description}
    {index : Nat} {terminal : Cursor checked} :
    {owner name : String} → {path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name} →
    {record : RecordIndex catalogue} → {invocation : Invocation catalogue record} → Binding queue path invocation →
    {original result : Subject artifact.sources} → GenericDutyQueue.Transport invocation.applications.reverse original result →
    {cursor : Cursor checked} → Paired checked native index cursor terminal → Type where
  | direct {owner name path record invocation}
      {binding : @Binding artifact.sources catalogue queue rootOwner rootName owner name path record invocation}
      {original result : Subject artifact.sources} (remaining : GenericDutyQueue.Transport invocation.applications.reverse original result)
      {cursor : Cursor checked} {paired : Paired checked native index cursor terminal}
      (node : GenericOperation.Node) (source : original.description.nodes[original.description.root]? = some node)
      (concrete : keyOf node = none) (nativeHead : wrapped cursor.node = false) :
      Chain binding remaining paired
  | formal {caller record} {event : SourceRuntimeContext.NamedEvent artifact.sources caller}
      {body : SourceRuntimeTrace.Body event.target.signature}
      {bodyRead : Computed (SourceRuntimeTrace.readNamedBody event) body}
      {parent : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName caller event.target.callerName}
      {invocation : Invocation catalogue record} {app : ApplicationAt catalogue record} {target : GenericDutyQueue.Target app}
      {prior : Binding queue parent invocation} {edge : Edge event parent app}
      {original result : Subject artifact.sources}
      {transport : GenericDutyQueue.Transport (Invocation.call invocation app target).applications.reverse original result}
      {cursor : Cursor checked} {paired : Paired checked native index cursor terminal}
      (hop : Selected event app.original (RuntimeFormalActual.splitInvocation invocation app target transport).transfer paired)
      (interior : {value : Interior hop prior (RuntimeFormalActual.splitInvocation invocation app target transport).tail //
        Computed (readInterior hop prior (RuntimeFormalActual.splitInvocation invocation app target transport).tail) value})
      (tail : Chain prior (RuntimeFormalActual.splitInvocation invocation app target transport).tail hop.wrapper.child) :
      Chain (Binding.named (body := body) (original := bodyRead) (target := target) prior edge) transport paired

private abbrev Reader {artifact catalogue context description graph implementations references prepared root requested}
    (checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested)
    (queue : GenericDutyQueue.Checked catalogue) (rootOwner rootName : String) (native : OperationDescription.Description)
    (index : Nat) (terminal : Cursor checked) :=
  {owner name : String} → {path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name} →
  {record : RecordIndex catalogue} → {invocation : Invocation catalogue record} → (binding : Binding queue path invocation) →
  {original result : Subject artifact.sources} → (transport : GenericDutyQueue.Transport invocation.applications.reverse original result) →
  {cursor : Cursor checked} → (paired : Paired checked native index cursor terminal) → WorkM (Chain binding transport paired)

private def visit {artifact catalogue context description graph implementations references prepared root requested}
    (checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested)
    (queue : GenericDutyQueue.Checked catalogue) (rootOwner rootName : String) (native : OperationDescription.Description)
    (index : Nat) (terminal : Cursor checked) : Nat → Reader checked queue rootOwner rootName native index terminal :=
  Nat.rec (motive := fun _ => Reader checked queue rootOwner rootName native index terminal)
    (fun {_ _ _ _ _} _ {_ _} _ {_} _ => throw .limit)
    (fun _ next {_ _ _ _ _} binding {original _} transport {cursor} paired => do
      exactWork (Exact.charge (16*(original.description.nodes.length+1)))
      match observed : original.description.nodes[original.description.root]? with
      | none => throw .request
      | some node =>
        match identity : keyOf node with
        | none =>
          if nativeHead : wrapped cursor.node = false then return .direct transport node observed identity nativeHead
          else throw .request
        | some key =>
          let source := observed.trans (congrArg some (keyOf_some identity))
          let some wrapper := unwrap paired | throw .request
          match binding,transport with
          | .root ..,_ => throw .request
          | .named (event := event) (invocation := invocation) (application := app) (target := target) prior _,receipt =>
            let pieces := RuntimeFormalActual.splitInvocation invocation app target receipt
            let choice ← NaturalAffine.witness (RuntimeFormalActual.readChoice wrapper.selected)
            let supply ← NaturalAffine.witness (RuntimeFormalActual.readSupply event app.original pieces.transfer key choice.val)
            let hop : Selected event app.original pieces.transfer paired :=
              ⟨key,source,wrapper,choice.val,by with_reducible exact choice.property,
                supply.val,by with_reducible exact supply.property,supply.val.returned⟩
            let interior ← NaturalAffine.witness (readInterior hop prior pieces.tail)
            let tail ← next prior pieces.tail hop.wrapper.child
            return .formal hop ⟨interior.val,by with_reducible exact interior.property⟩ tail)

def read {artifact catalogue context description graph implementations references prepared root requested checked
    queue rootOwner rootName owner name path record invocation original result native index cursor terminal}
    (binding : @Binding artifact.sources catalogue queue rootOwner rootName owner name path record invocation)
    (transport : GenericDutyQueue.Transport invocation.applications.reverse original result)
    (paired : @Paired artifact catalogue context description graph implementations references prepared root requested
      checked native index cursor terminal) : WorkM (Chain binding transport paired) := do
  let depth := invocation.depth
  exactWork (Exact.charge (16*(depth+1)))
  visit checked queue rootOwner rootName native index terminal (depth+1) binding transport paired

/-- Source-facing projection in innermost-to-outermost call order. -/
structure Hop where
  key : Parameter
  formalName : String
  position : Nat
  mixed : Nat
  tokens : List LocatedToken

private theorem callLength {sources catalogue record} (parent : @Invocation sources catalogue record)
    (application : ApplicationAt catalogue record) (target : GenericDutyQueue.Target application) :
    (Invocation.call parent application target).applications.length = parent.applications.length+1 := by
  simpa only [List.length_reverse,List.length_cons] using
    congrArg List.length (Invocation.call_reverse parent application target)

private abbrev Projection {artifact catalogue context description graph implementations references prepared root requested}
    (checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested)
    (queue : GenericDutyQueue.Checked catalogue) (rootOwner rootName : String) (native : OperationDescription.Description)
    (index : Nat) (terminal : Cursor checked) (fuel : Nat) :=
  {owner name : String} → {path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name} →
  {record : RecordIndex catalogue} → {invocation : Invocation catalogue record} → {binding : Binding queue path invocation} →
  {original result : Subject artifact.sources} → {transport : GenericDutyQueue.Transport invocation.applications.reverse original result} →
  {cursor : Cursor checked} → {paired : Paired checked native index cursor terminal} →
  Chain binding transport paired → invocation.applications.length ≤ fuel → List Hop

def Chain.hops {artifact catalogue context description graph implementations references prepared root requested checked
    queue rootOwner rootName owner name path record invocation original result native index cursor terminal}
    {binding : @Binding artifact.sources catalogue queue rootOwner rootName owner name path record invocation}
    {transport : GenericDutyQueue.Transport invocation.applications.reverse original result}
    {paired : @Paired artifact catalogue context description graph implementations references prepared root requested
      checked native index cursor terminal} (chain : Chain binding transport paired) : List Hop :=
  -- Each formal consumes one original application. A remaining formal at
  -- zero fuel is impossible by its actual invocation constructor.
  (Nat.rec (motive := Projection checked queue rootOwner rootName native index terminal)
    (fun {_ _ _ _ _ _ _ _ _ _ _} value => by
      cases value with
      | direct => exact fun _ => []
      | formal =>
        intro bound
        rw [callLength] at bound
        exact False.elim (Nat.not_succ_le_zero _ bound))
    (fun _ next {_ _ _ _ _ _ _ _ _ _ _} value => by
      cases value with
      | direct => exact fun _ => []
      | formal hop _ tail =>
        intro bound
        rw [callLength] at bound
        exact ⟨hop.key,hop.choice.header.name,hop.choice.position,hop.supply.source.index.val,
          hop.supply.source.actual.argument.tokens⟩ :: next tail (Nat.le_of_succ_le_succ bound))
    invocation.applications.length) chain (Nat.le_refl _)

end QleisliKernel.Qirf.RuntimeForwardedSupply
