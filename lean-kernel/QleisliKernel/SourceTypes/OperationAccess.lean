import QleisliKernel.SourceTypes.StaticOperation

/-! Original implementation-path demands for every operation occurrence.
This backwards traversal preserves mandatory inverse formation, original
formal premises and conservative provider dependencies, including unused
arguments and zero powers. Potential paths are not actual native evidence;
the enclosing gate must discharge each demanded provider implementation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.OperationAccess
open Finite OperationDescription StaticOperation

def empty : Paths := ⟨false,false,false⟩
def applicable : Paths := ⟨true,false,false⟩
def adjointable : Paths := ⟨false,true,false⟩
def controllable : Paths := ⟨false,false,true⟩

def join (left right : Paths) : Paths :=
  ⟨left.applicable || right.applicable,left.adjointable || right.adjointable,
    left.controllable || right.controllable⟩

def satisfies (available demanded : Paths) : Bool :=
  (!demanded.applicable || available.applicable) &&
    (!demanded.adjointable || available.adjointable) &&
    (!demanded.controllable || available.controllable)

def any (paths : Paths) : Bool := paths.applicable || paths.adjointable || paths.controllable

private def add (demands : Array Paths) (index : Nat) (paths : Paths) : WorkM (Array Paths) := do
  let some previous := demands[index]? | throw .request
  pure (demands.setIfInBounds index (join previous paths))

private def addActuals (operations : List (String × Nat)) (paths : Paths) (demands : Array Paths) :
    WorkM (Array Paths) := operations.foldlM (fun demands (_,index) => add demands index paths) demands

private def required (access : List (StaticHeaders.Access × String)) (name : String) : Paths :=
  ⟨access.contains (.applicable,name),access.contains (.adjointable,name),access.contains (.controllable,name)⟩

/-- Every original prerequisite is demanded even when no path on its provider
is requested. Available concrete actuals cannot supply undeclared formal paths. -/
private def originalPremises {sources : Sources} (provider : Provider sources)
    (operations : List (String × Nat)) (demands : Array Paths) : WorkM (Array Paths) := do
  match provider.signature.instantiation with
  | .closed _ =>
    guard operations.isEmpty .request
    pure demands
  | .static _ environment _ =>
    operations.foldlM (fun demands (name,index) =>
      add demands index (required environment.numeric.original.header.access name)) demands

private def formalActual {sources : Sources} (provider : Provider sources)
    (operations : List (String × Nat)) (ordinal : Nat) : WorkM Nat := do
  match provider.signature.instantiation with
  | .closed _ => throw .request
  | .static _ environment _ =>
    let some formal := environment.numeric.original.header.formals[ordinal]? | throw .request
    guard (formal.ordinal == ordinal) .request
    let .operation _ := formal.kind | throw .request
    let some (_,index) := operations.find? (·.1 == formal.name) | throw .request
    pure index

private def step {sources : Sources} (node : Node) (result : Result sources)
    (requested : Paths) (demands : Array Paths) : WorkM (Array Paths) := do
  guard (satisfies result.paths requested) .request
  match node with
  | .primitive .. => pure demands
  | .provider _ _ _ _ operations =>
    let some provider := result.provider | throw .request
    let demands ← originalPremises provider operations demands
    let demands ← if requested.adjointable then addActuals operations ⟨true,true,false⟩ demands
      else pure demands
    if requested.controllable then addActuals operations ⟨true,true,true⟩ demands else pure demands
  | .formal _ _ _ _ operations ordinal =>
    let some provider := result.formal | throw .request
    let demands ← originalPremises provider operations demands
    add demands (← formalActual provider operations ordinal) requested
  | .inverse child =>
    -- Formation itself requires J, including an unused/zero-power child.
    add demands child ⟨requested.adjointable,true,requested.controllable⟩
  | .controlled child =>
    add demands child (if any requested then controllable else empty)
  | .power child _ | .requested child _ _ => add demands child requested
  | .thenOp left right | .tensor left right =>
    add (← add demands left requested) right requested
  | .conjugate outer middle =>
    let demands ← add demands outer (if any requested then ⟨true,true,false⟩ else empty)
    add demands middle requested

/-- All edges point to earlier nodes, so a single reverse-order traversal
accumulates every demand before examining that node. It visits every node,
including provider children which runtime execution does not use. -/
def derive {sources context description} (graph : CheckedGraph sources context description)
    (requested : Paths) : WorkM (List Paths) := do
  exactWork (Exact.charge (64*(description.nodes.length+1)^2))
  let initial ← add (Array.replicate description.nodes.length empty) description.root requested
  let demands ← description.nodes.zipIdx.reverse.foldlM (fun demands (node,index) => do
    let some result := graph.results[index]? | throw .request
    let some requested := demands[index]? | throw .request
    step node result requested demands) initial
  pure demands.toList

structure Checked {sources context description} (graph : CheckedGraph sources context description)
    (requested : Paths) where
  demands : List Paths
  count : demands.length = description.nodes.length
  derived : ∃ before after, (derive graph requested).run before = (.ok demands,after)

def check {sources context description} (graph : CheckedGraph sources context description)
    (requested : Paths) : WorkM (Checked graph requested) := do
  let demands ← NaturalAffine.witness (derive graph requested)
  if count : demands.val.length = description.nodes.length then
    pure ⟨demands.val,count,by with_reducible exact demands.property⟩
  else throw .request

/-- Provider occurrences have the exact same order as graph.providers.
The native checker must prove actual Unitary inference for each demanded
J/C path and independently bind its inverse/controlled implementation. -/
def Checked.providers {sources context description graph requested}
    (checked : @Checked sources context description graph requested) : List (Provider sources × Paths) :=
  (graph.results.zip checked.demands).filterMap fun (result,paths) =>
    result.provider.map (fun provider => (provider,paths))

private def premiseAt {sources : Sources} (provider : Provider sources) (name : String) : Paths :=
  match provider.signature.instantiation with
  | .closed _ => empty
  | .static _ environment _ => required environment.numeric.original.header.access name

/-- Derive demands for CHILD EDGES, before any index union. Two occurrences
of a shared provider may bind different actual implementation subjects. -/
private def childrenAt {sources : Sources} (node : Node) (result : Result sources) (requested : Paths) :
    WorkM (List (Nat × Paths)) := do
  guard (satisfies result.paths requested) .request
  match node with
  | .primitive .. => pure []
  | .provider _ _ _ _ operations =>
    let some provider := result.provider | throw .request
    match provider.signature.instantiation with
    | .closed _ => guard operations.isEmpty .request
    | .static .. => pure ()
    let reverse := if requested.adjointable then ⟨true,true,false⟩ else empty
    let control := if requested.controllable then ⟨true,true,true⟩ else empty
    pure (operations.map fun (name,index) => (index,join (premiseAt provider name) (join reverse control)))
  | .formal _ _ _ _ operations ordinal =>
    let some provider := result.formal | throw .request
    match provider.signature.instantiation with
    | .closed _ => throw .request
    | .static _ environment _ =>
      let some formal := environment.numeric.original.header.formals[ordinal]? | throw .request
      let .operation _ := formal.kind | throw .request
      guard (formal.ordinal == ordinal && operations.any (·.1 == formal.name)) .request
      pure (operations.map fun (name,index) =>
        (index,join (premiseAt provider name) (if name == formal.name then requested else empty)))
  | .inverse child => pure [(child,⟨requested.adjointable,true,requested.controllable⟩)]
  | .controlled child => pure [(child,if any requested then controllable else empty)]
  | .power child _ | .requested child _ _ => pure [(child,requested)]
  | .thenOp left right | .tensor left right => pure [(left,requested),(right,requested)]
  | .conjugate outer middle => pure [(outer,if any requested then ⟨true,true,false⟩ else empty),(middle,requested)]

private inductive OccurrenceTask where
  | enter (index : Nat) (requested : Paths)
  | leave (index : Nat) (requested : Paths)

private def occurrenceLoop {sources context description} (graph : CheckedGraph sources context description) :
    Nat → List OccurrenceTask → List (Nat × Paths) → WorkM (List (Nat × Paths)) :=
  Nat.rec (fun tasks reversed => if tasks.isEmpty then pure reversed.reverse else throw .limit)
    (fun _ next tasks reversed => do
      exactWork (Exact.charge (8*(tasks.length+reversed.length+1)))
      match tasks with
      | [] => pure reversed.reverse
      | .enter index requested :: rest =>
        let some node := description.nodes[index]? | throw .request
        let some result := graph.results[index]? | throw .request
        let children ← childrenAt node result requested
        next (children.map (fun (index,paths) => .enter index paths) ++ [.leave index requested] ++ rest) reversed
      | .leave index requested :: rest => next rest ((index,requested) :: reversed))

def deriveOccurrences {sources context description} (graph : CheckedGraph sources context description)
    (requested : Paths) (order : List Nat) : WorkM (List (Nat × Paths)) := do
  guard (order.length ≤ 4096) .limit
  occurrenceLoop graph (2*order.length+1) [.enter description.root requested] []

structure CheckedOccurrences {sources context description} (graph : CheckedGraph sources context description)
    (requested : Paths) where
  order : List Nat
  originalOrder : ∃ before after,(StaticOperation.readOccurrences description).run before = (.ok order,after)
  demands : List (Nat × Paths)
  sameOrder : demands.map (·.1) = order
  bounded : demands.length ≤ 4096
  derived : ∃ before after,(deriveOccurrences graph requested order).run before = (.ok demands,after)

def checkOccurrences {sources context description} (graph : CheckedGraph sources context description)
    (requested : Paths) : WorkM (CheckedOccurrences graph requested) := do
  let order ← NaturalAffine.witness (StaticOperation.readOccurrences description)
  let demands ← NaturalAffine.witness (deriveOccurrences graph requested order.val)
  if sameOrder : demands.val.map (·.1) = order.val then
    if bounded : demands.val.length ≤ 4096 then
      pure ⟨order.val,by with_reducible exact order.property,demands.val,sameOrder,bounded,
        by with_reducible exact demands.property⟩
    else throw .limit
  else throw .request

/-- Exact per-occurrence provider subjects, in the same expanded postorder as
the complete body and Meaning queues. Duplicate source indices remain distinct. -/
def CheckedOccurrences.providers {sources context description graph requested}
    (checked : @CheckedOccurrences sources context description graph requested) :
    List (Nat × Provider sources × Paths) :=
  checked.demands.filterMap fun (index,paths) => do
    let result ← graph.results[index]?
    let provider ← result.provider
    pure (index,provider,paths)

theorem join_empty (paths : Paths) : join paths empty = paths := by
  cases paths with | mk a j c => simp [join,empty]

theorem satisfies_empty (paths : Paths) : satisfies paths empty = true := by
  simp [satisfies,empty]

end QleisliKernel.SourceTypes.OperationAccess
