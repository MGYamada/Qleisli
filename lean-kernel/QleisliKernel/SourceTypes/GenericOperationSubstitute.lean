import QleisliKernel.SourceTypes.GenericOperation
import QleisliKernel.SourceTypes.SymbolicTypes
import QleisliKernel.SourceTypes.NaturalSubstitute

/-! One simultaneous transport of an original callee operation closure.
The input ApplicationSource retains the original static argument occurrence
and premise-transfer witness. Existing proof-producing Basis/Nat substitution
is reused. An inserted Op actual is not traversed as another callee template.
Original supplier environments and guard scopes remain attached to every node.
This module classifies metadata; it proves no Meaning equation, implementation
path, complete invocation expansion or native admission.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.GenericOperationSubstitute
open Finite GenericOperation Semantics.SymbolicBasis Semantics.SourceAffine

def callerFrame {sources} (application : ApplicationSource sources) : NaturalFrames.Frame :=
  StaticHeaders.frame application.state.prepared.original

def calleeFrame {sources} (application : ApplicationSource sources) : NaturalFrames.Frame :=
  StaticHeaders.frame application.target

structure Subject (sources : Sources) where
  description : Description
  suppliers : List (Nat × Origin sources)

def basisKeys {sources} (application : ApplicationSource sources) : List Parameter :=
  application.target.header.formals.filterMap fun formal => match formal.kind with
    | .basis => some ⟨application.owner,application.name,formal.ordinal⟩
    | _ => none

def operationKeys {sources} (application : ApplicationSource sources) : List Parameter :=
  application.target.header.formals.filterMap fun formal => match formal.kind with
    | .operation _ => some ⟨application.owner,application.name,formal.ordinal⟩
    | _ => none

/-- These equalities authenticate mixed-kind positions and canonical Nat
replacement order. They select no convenient value for an original formal. -/
structure Context {sources} (application : ApplicationSource sources) : Type where
  bases : application.basisActuals.map (·.1) = basisKeys application
  operations : application.operationActuals.map (·.original) = operationKeys application
  naturals : application.naturalActuals =
    NaturalFrames.replacements (StaticHeaders.frame application.transfer.callee.original)
      (application.transfer.forms.map (·.form))
  dimensions : application.naturalActuals.all
    (fun form => form.coefficients.length == (callerFrame application).binders.length) = true
  frames : application.operationActuals.all (fun actual =>
    actual.subject.frame.binders == (callerFrame application).binders &&
      actual.subject.nodeFrames.length == actual.subject.nodes.length &&
      actual.subject.nodeFrames.all (fun frame => frame.binders == (callerFrame application).binders)) = true

private def actualFields {sources} (application : ApplicationSource sources) : Nat :=
  (application.basisActuals.map fun (key,code) => Meter.key key+Meter.basis code+1).sum+
    (application.naturalActuals.map Meter.form).sum+
    (application.operationActuals.map fun actual =>
      Meter.key actual.original+Meter.payload actual.subject+actual.suppliers.length+1).sum

def readContext {sources} (application : ApplicationSource sources) : WorkM (Context application) := do
  let formals := application.target.header.formals.length
  let keyBytes := application.owner.utf8ByteSize+application.name.utf8ByteSize+3
  let frames := (application.operationActuals.map fun actual => actual.subject.nodeFrames.length+1).sum
  exactWork (Exact.charge (16*(actualFields application+formals*formals+
    (application.basisActuals.length+application.operationActuals.length+1)*(keyBytes+1)+
    (frames+1)*(Meter.frame (callerFrame application)+1)+Meter.frame (calleeFrame application)+1)))
  if bases : application.basisActuals.map (·.1) = basisKeys application then
    if operations : application.operationActuals.map (·.original) = operationKeys application then
      if naturals : application.naturalActuals =
          NaturalFrames.replacements (StaticHeaders.frame application.transfer.callee.original)
            (application.transfer.forms.map (·.form)) then
        if dimensions : application.naturalActuals.all
            (fun form => form.coefficients.length == (callerFrame application).binders.length) = true then
          if frames : application.operationActuals.all (fun actual =>
              actual.subject.frame.binders == (callerFrame application).binders &&
                actual.subject.nodeFrames.length == actual.subject.nodes.length &&
                actual.subject.nodeFrames.all (fun frame => frame.binders == (callerFrame application).binders)) = true then
            return ⟨bases,operations,naturals,dimensions,frames⟩
          else throw .request
        else throw .request
      else throw .request
    else throw .request
  else throw .request

structure BasisStep {sources} (application : ApplicationSource sources) where
  original : Code
  checked : SymbolicTypes.Substituted application.basisActuals application.naturalActuals original
  computed : ∃ before after,
    (SymbolicTypes.substitute (callerFrame application).binders.length
      application.basisActuals application.naturalActuals original).run before = (.ok checked,after)

structure NaturalStep {sources} (application : ApplicationSource sources) where
  original : Form
  checked : NaturalSubstitute.Result original application.naturalActuals
  computed : ∃ before after,
    (NaturalSubstitute.substitute (callerFrame application).binders.length original
      application.naturalActuals).run before = (.ok checked,after)

def basis {sources} (application : ApplicationSource sources) (code : Code) :
    WorkM (BasisStep application) := do
  let checked ← NaturalAffine.witness (SymbolicTypes.substitute (callerFrame application).binders.length
    application.basisActuals application.naturalActuals code)
  return ⟨code,checked.val,by with_reducible exact checked.property⟩

def natural {sources} (application : ApplicationSource sources) (form : Form) :
    WorkM (NaturalStep application) := do
  let checked ← NaturalAffine.witness (NaturalSubstitute.substitute (callerFrame application).binders.length
    form application.naturalActuals)
  return ⟨form,checked.val,by with_reducible exact checked.property⟩

structure NodeResult {sources} (application : ApplicationSource sources) where
  subject : Subject sources
  bases : List (BasisStep application)
  naturals : List (NaturalStep application)

def roots {sources} (original : Subject sources) (index root : Nat) : List (Nat × Origin sources) :=
  (original.suppliers.filter (·.1 == index)).map (fun (_,origin) => (root,origin))

private def reserve {sources} (subjects : List (Subject sources)) : WorkM Unit := do
  let count := (subjects.map (·.description.nodes.length)).sum+1
  guard (count ≤ 4096) .limit
  exactWork (Exact.charge (16*(count+(subjects.map fun subject =>
    Meter.payload subject.description+subject.suppliers.length).sum+1)))

private def unary {sources} (application : ApplicationSource sources) (original : Subject sources)
    (index : Nat) (child : Subject sources) (constructor : Nat → Node) : WorkM (Subject sources) := do
  reserve [child]
  guard (child.description.frame.binders == (callerFrame application).binders) .request
  let description := child.description.unary constructor
  return ⟨description,child.suppliers ++ roots original index description.root⟩

private def binary {sources} (original : Subject sources) (index : Nat)
    (left right : Subject sources) (constructor : Nat → Nat → Node) : WorkM (Subject sources) := do
  reserve [left,right]
  guard (left.description.frame.binders == right.description.frame.binders) .request
  let description := left.description.binary right.description constructor
  return ⟨description,left.suppliers ++ right.suppliers.map (fun (index,origin) =>
    (index+left.description.nodes.length,origin)) ++ roots original index description.root⟩

def readNode {sources} (application : ApplicationSource sources) (original : Subject sources)
    (previous : List (Subject sources)) (index : Nat) (node : Node) : WorkM (NodeResult application) := do
  exactWork (Exact.charge (16*(Meter.node node+actualFields application+
    original.suppliers.length+previous.length+1)*
      ((callerFrame application).binders.length+application.target.header.formals.length+1)))
  let child (index : Nat) := lift (readOption previous[index]?)
  let frame := callerFrame application
  match node with
  | .formal key =>
    match application.operationActuals.find? (·.original == key) with
    | some actual =>
      -- Simultaneous substitution: this is the exact caller closure, including
      -- its own original keys and supplier contexts. Do not recurse into it.
      return ⟨⟨actual.subject,actual.suppliers⟩,[],[]⟩
    | none =>
      let description := Description.singleton frame (.formal key)
      return ⟨⟨description,roots original index 0⟩,[],[]⟩
  | .primitive kind target =>
    let replaced ← basis application target
    let description := Description.singleton frame (.primitive kind replaced.checked.code)
    return ⟨⟨description,roots original index 0⟩,[replaced],[]⟩
  | .provider owner name bases naturals operations premises =>
    let bases ← bases.mapM fun (name,code) => do
      let replaced ← basis application code
      pure (name,replaced)
    let naturals ← naturals.mapM fun (name,form) => do
      let replaced ← natural application form
      pure (name,replaced)
    let operations ← operations.mapM fun (name,index) => do
      let value ← child index
      pure (name,value)
    reserve (operations.map (·.2))
    let description := GenericOperation.provider frame owner name
      (bases.map fun (name,replaced) => (name,replaced.checked.code))
      (naturals.map fun (name,replaced) => (name,replaced.checked.form))
      (operations.map fun (name,value) => (name,value.description)) premises
    let (_,suppliers) := operations.foldl (fun (offset,suppliers) (_,value) =>
      (offset+value.description.nodes.length,
        suppliers ++ value.suppliers.map (fun (index,origin) => (index+offset,origin)))) (0,[])
    return ⟨⟨description,suppliers ++ roots original index description.root⟩,
      bases.map (·.2),naturals.map (·.2)⟩
  | .inverse index' =>
    return ⟨← unary application original index (← child index') .inverse,[],[]⟩
  | .controlled index' =>
    return ⟨← unary application original index (← child index') .controlled,[],[]⟩
  | .requested index' owner name =>
    return ⟨← unary application original index (← child index') (fun child => .requested child owner name),[],[]⟩
  | .power index' count =>
    let replaced ← natural application count.form
    let subject ← unary application original index (← child index')
      (fun child => .power child ⟨replaced.checked.form,count.powerTwo⟩)
    return ⟨subject,[],[replaced]⟩
  | .thenOp left right =>
    return ⟨← binary original index (← child left) (← child right) .thenOp,[],[]⟩
  | .tensor left right =>
    return ⟨← binary original index (← child left) (← child right) .tensor,[],[]⟩
  | .conjugate outer middle =>
    return ⟨← binary original index (← child outer) (← child middle) .conjugate,[],[]⟩

structure Step {sources} (application : ApplicationSource sources) (original : Subject sources) where
  index : Nat
  node : Node
  actual : original.description.nodes[index]? = some node
  previous : List (Subject sources)
  result : NodeResult application
  computed : ∃ before after,(readNode application original previous index node).run before = (.ok result,after)

/-- The actual executable formal branch either inserts the whole selected
caller closure or retains the original unbound key. It applies no further
Basis/Nat/Op substitution to the inserted subject or its supplier contexts. -/
theorem Step.formal_result {sources application original} (step : @Step sources application original)
    {key : Parameter} (formal : step.node = .formal key) :
    step.result = match application.operationActuals.find? (·.original == key) with
      | some actual => ⟨⟨actual.subject,actual.suppliers⟩,[],[]⟩
      | none => ⟨⟨Description.singleton (callerFrame application) (.formal key),roots original step.index 0⟩,[],[]⟩ := by
  obtain ⟨before,after,ran⟩ := step.computed
  rw [formal] at ran
  unfold readNode at ran
  obtain ⟨_,_,_,returned⟩ := bind_success _ _ _ _ _ ran
  cases found : application.operationActuals.find? (·.original == key) <;>
    simp only [found] at returned <;> exact (pure_success _ _ _ _ returned).1

/-- The lookup position in operationActuals counts Op entries; the Parameter
stored at that position uses the ordinal in the original mixed-kind header. -/
structure FormalSelection {sources application original} (step : @Step sources application original)
    (key : Parameter) (actual : ActualOperation sources) : Prop where
  source : original.description.nodes[step.index]? = some (.formal key)
  first : application.operationActuals[application.operationActuals.findIdx (·.original == key)]? = some actual
  originalKey : actual.original = key
  keyAt : (operationKeys application)[application.operationActuals.findIdx (·.original == key)]? = some key
  mixedFormal : ∃ formal ∈ application.target.header.formals, ∃ tokens,
    formal.kind = .operation tokens ∧ key = ⟨application.owner,application.name,formal.ordinal⟩
  returned : step.result = ⟨⟨actual.subject,actual.suppliers⟩,[],[]⟩

private instance : ReflBEq Parameter := ⟨by deriving_ReflEq_tactic⟩
private instance : LawfulBEq Parameter := ⟨by deriving_LawfulEq_tactic⟩

theorem Step.formal_selection {sources application original} (step : @Step sources application original)
    (context : Context application) {key : Parameter} (formal : step.node = .formal key)
    {actual : ActualOperation sources} (found : application.operationActuals.find? (·.original == key) = some actual) :
    FormalSelection step key actual := by
  have keyEq : actual.original = key :=
    eq_of_beq (List.find?_some (p := fun choice : ActualOperation sources => choice.original == key) found)
  have first := List.find?_eq_getElem?_findIdx.symm.trans found
  have present : key ∈ operationKeys application := by
    rw [← context.operations,← keyEq]
    exact List.mem_map_of_mem (f := ActualOperation.original) (List.mem_of_find?_eq_some found)
  refine ⟨by simpa only [formal] using step.actual,first,keyEq,?_,?_,?_⟩
  · rw [← context.operations,List.getElem?_map,first,Option.map_some,keyEq]
  · obtain ⟨binder,member,selected⟩ := List.mem_filterMap.mp present
    cases kind : binder.kind with
    | basis => simp [kind] at selected
    | natural => simp [kind] at selected
    | operation tokens =>
      exact ⟨binder,member,tokens,kind,by simpa only [kind,Option.some.injEq] using selected.symm⟩
  · simpa only [found] using step.formal_result formal

/-- A declared Op key in the authenticated mixed header necessarily reaches
the insertion branch, including when the actual itself contains open keys. -/
theorem Step.formal_selection_of_mem {sources application original} (step : @Step sources application original)
    (context : Context application) {key : Parameter} (formal : step.node = .formal key)
    (present : key ∈ operationKeys application) : ∃ actual, FormalSelection step key actual := by
  rw [← context.operations] at present
  obtain ⟨candidate,member,same⟩ := List.mem_map.mp present
  cases found : application.operationActuals.find? (·.original == key) with
  | some actual => exact ⟨actual,step.formal_selection context formal found⟩
  | none =>
    have excluded := List.find?_eq_none.mp found candidate member
    simp [same] at excluded

structure Result {sources} (application : ApplicationSource sources) (original : Subject sources) where
  subject : Subject sources
  steps : List (Step application original)
  every : steps.map (·.index) = List.range original.description.nodes.length
  returned : steps[original.description.root]?.map (·.result.subject) = some subject

private def run {sources} (application : ApplicationSource sources) (original : Subject sources) :
    WorkM (Result application original) := do
  exactWork (Exact.charge (Meter.rebuildWork original.description))
  guard (!original.description.nodes.isEmpty && original.description.nodes.length ≤ 4096 &&
    original.description.root+1 == original.description.nodes.length &&
    original.description.nodeFrames.length == original.description.nodes.length &&
    original.description.nodeFrames.all (fun frame => frame.binders == (calleeFrame application).binders) &&
    original.description.frame.binders == (calleeFrame application).binders &&
    original.description.nodes.zipIdx.all (fun (node,index) => node.children.all (· < index))) .request
  let (_previous,steps) ← (List.range original.description.nodes.length).foldlM
    (fun (previous,steps) index => do
      match actual : original.description.nodes[index]? with
      | none => throw .request
      | some node =>
        let result ← NaturalAffine.witness (readNode application original previous index node)
        have same : original.description.nodes[index]? = some node := by
          first | exact actual | rfl
        let step : Step application original := ⟨index,node,same,previous,
          result.val,by with_reducible exact result.property⟩
        pure (previous ++ [result.val.subject],steps ++ [step])) ([],[])
  if every : steps.map (·.index) = List.range original.description.nodes.length then
    match returned : steps[original.description.root]?.map (·.result.subject) with
    | none => throw .request
    | some returnedSubject =>
      -- Subject contains functions in retained Origins; compare no such data.
      -- Select the exact same Step projection that the executable fold built.
      return ⟨returnedSubject,steps,every,by first | exact returned | rfl⟩
  else throw .request

structure Checked {sources} (application : ApplicationSource sources) (original : Subject sources) where
  context : Context application
  prepared : ∃ before after,(readContext application).run before = (.ok context,after)
  result : Result application original
  computed : ∃ before after,(run application original).run before = (.ok result,after)

/-- One actual setup for this exact original application. The retained
execution authenticates all simultaneous mixed-key maps and original frames;
it contains no translated subject, closure result or native proof. -/
structure Prepared {sources} (application : ApplicationSource sources) : Type where
  context : Context application
  original : ∃ before after,(readContext application).run before = (.ok context,after)

def prepare {sources} (application : ApplicationSource sources) : WorkM (Prepared application) := do
  let context ← NaturalAffine.witness (readContext application)
  return ⟨context.val,by with_reducible exact context.property⟩

def readWithPrepared {sources application} (prepared : @Prepared sources application)
    (description : Description) (suppliers : List (Nat × Origin sources)) :
    WorkM (Checked application ⟨description,suppliers⟩) := do
  let result ← NaturalAffine.witness (run application ⟨description,suppliers⟩)
  return ⟨prepared.context,prepared.original,result.val,by with_reducible exact result.property⟩

def read {sources} (application : ApplicationSource sources) (description : Description)
    (suppliers : List (Nat × Origin sources)) : WorkM (Checked application ⟨description,suppliers⟩) := do
  readWithPrepared (← prepare application) description suppliers

structure DutyChecked {sources} (application : ApplicationSource sources) (original : Duty sources) where
  subject : Checked application ⟨original.subject,original.suppliers⟩

/-- The original assertion, lexical guard environment and binding chain stay
indexed inputs. The result supplies one additional call binding; an enclosing
catalogue expansion must authenticate that call's target original body and
retain this wrapper instead of treating the translated descriptor as evidence. -/
def readDuty {sources} (application : ApplicationSource sources) (original : Duty sources) :
    WorkM (DutyChecked application original) := do
  let subject ← read application original.subject original.suppliers
  return ⟨subject⟩

private theorem finiteFoldInvariant {α β : Type} (p : β → Prop) (f : β → α → WorkM β)
    (keep : ∀ state item next before after, p state →
      (f state item).run before = (.ok next,after) → p next)
    (items : List α) {initial final : β} {before after : Nat} (valid : p initial)
    (ran : (items.foldlM f initial).run before = (.ok final,after)) : p final := by
  induction items generalizing initial before with
  | nil =>
    simp only [List.foldlM_nil] at ran
    rw [(pure_success _ _ _ _ ran).1]
    exact valid
  | cons item rest ih =>
    simp only [List.foldlM_cons] at ran
    obtain ⟨next,middle,one,tail⟩ := bind_success _ _ _ _ _ ran
    exact ih (keep initial item next before middle valid one) tail

private def Prefixes {sources application original}
    (previous : List (Subject sources)) (rows : List (@Step sources application original)) : Prop :=
  previous = rows.map (·.result.subject) ∧
    ∀ i row, rows[i]? = some row → row.previous = (rows.take i).map (·.result.subject)

private theorem prefixes_append {sources application original} {previous : List (Subject sources)}
    {rows : List (@Step sources application original)} (valid : Prefixes previous rows)
    (added : Step application original) (prior : added.previous = previous) :
    Prefixes (previous ++ [added.result.subject]) (rows ++ [added]) := by
  obtain ⟨values,oldRows⟩ := valid
  constructor
  · simp only [List.map_append,List.map_cons,List.map_nil,values]
  · intro i row selected
    by_cases old : i < rows.length
    · rw [List.getElem?_append_left old] at selected
      rw [List.take_append_of_le_length (Nat.le_of_lt old)]
      exact oldRows i row selected
    · obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp selected
      simp only [List.length_append,List.length_singleton] at bound
      have atEnd : i = rows.length := by omega
      subst i
      rw [List.getElem?_append_right (Nat.le_refl rows.length)] at selected
      have same : added = row := by simpa using selected
      rw [List.take_left,← same]
      exact prior.trans values

/-- The successful simultaneous substitution reads each child from the projected
results of the strictly preceding steps of this execution, in their original order. -/
theorem Checked.previous_eq {sources application original} (checked : @Checked sources application original)
    (i : Nat) {step : Step application original} (selected : checked.result.steps[i]? = some step) :
    step.previous = (checked.result.steps.take i).map (·.result.subject) := by
  obtain ⟨_,_,ran⟩ := checked.computed
  unfold run at ran
  obtain ⟨_,_,_,tail⟩ := bind_success _ _ _ _ _ ran
  obtain ⟨_,_,_,tail⟩ := bind_success _ _ _ _ _ tail
  obtain ⟨⟨previous,rows⟩,_,folded,finish⟩ := bind_success _ _ _ _ _ tail
  have valid : Prefixes previous rows := by
    refine finiteFoldInvariant
      (fun pair : List (Subject sources) × List (Step application original) => Prefixes pair.1 pair.2)
      _ ?_ _ ?_ folded
    · rintro ⟨prev,steps⟩ index next before after kept one
      dsimp only at one
      split at one
      · cases one
      · obtain ⟨result,_,_,appended⟩ := bind_success _ _ _ _ _ one
        have same := (pure_success _ _ _ _ appended).1
        subst next
        refine prefixes_append kept ⟨index,_,?_,prev,result.val,?_⟩ rfl
    · exact ⟨rfl,by simp⟩
  dsimp only at finish
  split at finish
  · split at finish
    · cases finish
    · have same := (pure_success _ _ _ _ finish).1
      have actualRows : checked.result.steps = rows := congrArg Result.steps same
      rw [actualRows] at selected ⊢
      exact valid.2 i step selected
  · cases finish

/-- A selected step stores the exact index of its original source node. -/
theorem Result.index_at {sources application original} (result : @Result sources application original)
    {i : Nat} {step : Step application original} (selected : result.steps[i]? = some step) :
    step.index = i := by
  have size := congrArg List.length result.every
  simp only [List.length_map,List.length_range] at size
  have bound := (List.getElem?_eq_some_iff.mp selected).choose
  rw [size] at bound
  have atIndex := congrArg (fun xs : List Nat => xs[i]?) result.every
  simpa only [List.getElem?_map,selected,Option.map_some,List.getElem?_range bound,Option.some.injEq]
    using atIndex

/-- Both reads refer to the same checked substitution step. In particular a
second use of an equal-looking subject cannot select a different original index. -/
structure UsedChild {sources application original} (checked : @Checked sources application original)
    (parent : Step application original) (index : Nat) (child : Step application original) : Prop where
  atIndex : checked.result.steps[index]? = some child
  originalIndex : child.index = index
  previous : parent.previous[index]? = some child.result.subject

theorem Checked.child_at {sources application original} (checked : @Checked sources application original)
    {i index : Nat} {parent : Step application original} {subject : Subject sources}
    (parentAt : checked.result.steps[i]? = some parent) (used : parent.previous[index]? = some subject) :
    ∃ child, UsedChild checked parent index child ∧ child.result.subject = subject := by
  have inPrefix := used
  rw [checked.previous_eq i parentAt,List.getElem?_map] at inPrefix
  cases found : (checked.result.steps.take i)[index]? with
  | none => simp [found] at inPrefix
  | some child =>
    have equal : child.result.subject = subject := by simpa only [found,Option.map_some,Option.some.injEq] using inPrefix
    have inside := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp found).choose (List.length_take_le _ _)
    have atIndex := (List.getElem?_take_of_lt (l := checked.result.steps) inside).symm.trans found
    exact ⟨child,⟨atIndex,checked.result.index_at atIndex,by rw [equal]; exact used⟩,equal⟩

inductive BinaryConstructor : (Nat → Nat → Node) → Prop where
  | thenOp : BinaryConstructor .thenOp
  | tensor : BinaryConstructor .tensor
  | conjugate : BinaryConstructor .conjugate

structure BinaryChildren {sources application original} (checked : @Checked sources application original)
    (parent : Step application original) (l r : Nat) (constructor : Nat → Nat → Node)
    (leftStep rightStep : Step application original) : Prop where
  left : UsedChild checked parent l leftStep
  right : UsedChild checked parent r rightStep
  description : parent.result.subject.description =
    leftStep.result.subject.description.binary rightStep.result.subject.description constructor
  suppliers : parent.result.subject.suppliers = leftStep.result.subject.suppliers ++
    rightStep.result.subject.suppliers.map (fun (j,origin) => (j+leftStep.result.subject.description.nodes.length,origin)) ++
    roots original parent.index parent.result.subject.description.root

theorem readOption_selected {α : Type} {option : Option α} {value : α} {before after : Nat}
    (ran : (lift (readOption option)).run before = (.ok value,after)) : option = some value := by
  have success := (lift_success _ _ _ _ ran).1
  cases option <;> simp_all [readOption]

/-- The actual binary reader uses left and right in source order and appends
every supplier, including repeated ones, with the same shift as the right graph. -/
theorem Checked.binary_children {sources application original} (checked : @Checked sources application original)
    {i l r : Nat} {parent : Step application original} {constructor : Nat → Nat → Node}
    (parentAt : checked.result.steps[i]? = some parent) (kind : BinaryConstructor constructor)
    (source : parent.node = constructor l r) :
    ∃ left right, BinaryChildren checked parent l r constructor left right := by
  obtain ⟨_,after,ran⟩ := parent.computed
  rw [source] at ran
  unfold readNode at ran
  obtain ⟨_,start,_,body⟩ := bind_success _ _ _ _ _ ran
  have program : ((do
      let left ← lift (readOption parent.previous[l]?)
      let right ← lift (readOption parent.previous[r]?)
      let subject ← binary original parent.index left right constructor
      pure (⟨subject,[],[]⟩ : NodeResult application)) : WorkM _).run start = (.ok parent.result,after) := by
    cases kind <;> exact body
  obtain ⟨leftValue,_,readLeft,readRemaining⟩ := bind_success _ _ _ _ _ program
  obtain ⟨rightValue,_,readRight,buildRemaining⟩ := bind_success _ _ _ _ _ readRemaining
  obtain ⟨assembled,_,built,pureResult⟩ := bind_success _ _ _ _ _ buildRemaining
  have output : parent.result = ⟨assembled,[],[]⟩ := (pure_success _ _ _ _ pureResult).1
  obtain ⟨left,leftAt,leftEq⟩ := checked.child_at parentAt (readOption_selected readLeft)
  obtain ⟨right,rightAt,rightEq⟩ := checked.child_at parentAt (readOption_selected readRight)
  subst leftValue
  subst rightValue
  have subject : parent.result.subject = assembled := congrArg NodeResult.subject output
  unfold binary at built
  obtain ⟨_,_,_,built⟩ := bind_success _ _ _ _ _ built
  obtain ⟨_,_,_,built⟩ := bind_success _ _ _ _ _ built
  have returned := subject.trans (pure_success _ _ _ _ built).1
  exact ⟨left,right,leftAt,rightAt,congrArg Subject.description returned,by rw [returned]⟩

inductive UnaryConstructor : (Nat → Node) → Prop where
  | inverse : UnaryConstructor .inverse
  | controlled : UnaryConstructor .controlled
  | requested (owner name : String) : UnaryConstructor (fun j => .requested j owner name)

structure UnaryChild {sources application original} (checked : @Checked sources application original)
    (parent : Step application original) (index : Nat) (constructor : Nat → Node)
    (childStep : Step application original) : Prop where
  child : UsedChild checked parent index childStep
  description : parent.result.subject.description = childStep.result.subject.description.unary constructor
  suppliers : parent.result.subject.suppliers = childStep.result.subject.suppliers ++
    roots original parent.index parent.result.subject.description.root

private theorem Checked.unary_built {sources application original} (checked : @Checked sources application original)
    {i index before after : Nat} {parent : Step application original} {value assembled : Subject sources}
    {constructor : Nat → Node} (parentAt : checked.result.steps[i]? = some parent)
    (used : parent.previous[index]? = some value)
    (built : (unary application original parent.index value constructor).run before = (.ok assembled,after))
    (subject : parent.result.subject = assembled) :
    ∃ child, UnaryChild checked parent index constructor child := by
  obtain ⟨child,childAt,childEq⟩ := checked.child_at parentAt used
  subst value
  unfold unary at built
  obtain ⟨_,_,_,built⟩ := bind_success _ _ _ _ _ built
  obtain ⟨_,_,_,built⟩ := bind_success _ _ _ _ _ built
  have returned := subject.trans (pure_success _ _ _ _ built).1
  exact ⟨child,childAt,congrArg Subject.description returned,by rw [returned]⟩

theorem Checked.unary_child {sources application original} (checked : @Checked sources application original)
    {i index : Nat} {parent : Step application original} {constructor : Nat → Node}
    (parentAt : checked.result.steps[i]? = some parent) (kind : UnaryConstructor constructor)
    (source : parent.node = constructor index) :
    ∃ child, UnaryChild checked parent index constructor child := by
  obtain ⟨_,after,ran⟩ := parent.computed
  rw [source] at ran
  unfold readNode at ran
  obtain ⟨_,start,_,body⟩ := bind_success _ _ _ _ _ ran
  have program : ((do
      let value ← lift (readOption parent.previous[index]?)
      let subject ← unary application original parent.index value constructor
      pure (⟨subject,[],[]⟩ : NodeResult application)) : WorkM _).run start = (.ok parent.result,after) := by
    cases kind <;> exact body
  obtain ⟨_,_,used,body⟩ := bind_success _ _ _ _ _ program
  obtain ⟨assembled,_,built,body⟩ := bind_success _ _ _ _ _ body
  have output : parent.result = ⟨assembled,[],[]⟩ := (pure_success _ _ _ _ body).1
  exact checked.unary_built parentAt (readOption_selected used) built (congrArg NodeResult.subject output)

/-- The original child is read even for zero power. Its constructor receives
the exact retained Nat replacement and the original exponent mode. -/
theorem Checked.power_child {sources application original} (checked : @Checked sources application original)
    {i index : Nat} {parent : Step application original} {count : Count}
    (parentAt : checked.result.steps[i]? = some parent) (source : parent.node = .power index count) :
    ∃ (child : Step application original) (replacement : NaturalStep application), replacement.original = count.form ∧
      parent.result.naturals = [replacement] ∧ UnaryChild checked parent index
        (fun j => .power j ⟨replacement.checked.form,count.powerTwo⟩) child := by
  obtain ⟨_,_,ran⟩ := parent.computed
  rw [source] at ran
  unfold readNode at ran
  obtain ⟨_,_,_,body⟩ := bind_success _ _ _ _ _ ran
  obtain ⟨replacement,_,naturalRun,body⟩ := bind_success _ _ _ _ _ body
  obtain ⟨_,_,used,body⟩ := bind_success _ _ _ _ _ body
  obtain ⟨assembled,_,built,body⟩ := bind_success _ _ _ _ _ body
  have output : parent.result = ⟨assembled,[],[replacement]⟩ := (pure_success _ _ _ _ body).1
  obtain ⟨child,childRead⟩ := checked.unary_built parentAt (readOption_selected used) built
    (congrArg NodeResult.subject output)
  unfold natural at naturalRun
  obtain ⟨_,_,_,naturalReturn⟩ := bind_success _ _ _ _ _ naturalRun
  have naturalEq := (pure_success _ _ _ _ naturalReturn).1
  exact ⟨child,replacement,congrArg NaturalStep.original naturalEq,congrArg NodeResult.naturals output,childRead⟩

end QleisliKernel.SourceTypes.GenericOperationSubstitute
