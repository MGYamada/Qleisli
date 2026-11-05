import QleisliKernel.Qirf.RuntimeOperationTree
import QleisliKernel.Qirf.RuntimeSourceOperationMarkers
import QleisliKernel.SourceTypes.QuantumArms

/-! A genuine indexed original coherent arm uses the shared graph checker.
Its written ordinal and source graph come only from the retained QuantumArms
table. Forward bodies, actual C implementation evidence and complete Meaning
graphs use the same final root. Constructed arms also associate every written
source assertion with that same native occurrence's existing Meaning equation.
This adds no selector/sector or caller equation,
global catalogue discharge, wire reader or execution authority.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimePreparedArm
open QleisliKernel Finite SourceTypes
abbrev Request := RuntimeProviderHeader.Request

structure Prepared (artifact : Artifact) (catalogue : GenericCatalogue.Checked artifact.sources)
    {owner name offset selector target}
    (table : QuantumArms.Table artifact.sources owner name offset selector target)
    (index : Fin table.arms.length) (implementations : List Request) (references : List (List Request)) where
  graph : RuntimePreparedOperation.GraphPrepared artifact catalogue
    (table.arms[index.val]'index.isLt).operation.graph implementations references
  original : RuntimeInterval.Computed
    (RuntimePreparedOperation.prepareGraph artifact catalogue
      (table.arms[index.val]'index.isLt).operation.graph implementations references) graph
  relevance : SourceRows.Retained
    ([(owner,table.site.original.source)] ++ (table.arms[index.val]'index.isLt).sourceRows ++ graph.rows)

/-- The exact original label is independent of written table order. Neither
a transported name nor a supplied physical width chooses the selected arm. -/
def Prepared.label {artifact catalogue owner name offset selector target table index implementations references}
    (_prepared : @Prepared artifact catalogue owner name offset selector target table index implementations references) : Nat :=
  (table.arms[index.val]'index.isLt).label.ordinal

def Prepared.rows {artifact catalogue owner name offset selector target table index implementations references}
    (prepared : @Prepared artifact catalogue owner name offset selector target table index implementations references) : List SourceRows.Row :=
  prepared.relevance.rows

def Prepared.roots {artifact catalogue owner name offset selector target table index implementations references}
    (prepared : @Prepared artifact catalogue owner name offset selector target table index implementations references) : List Nat :=
  prepared.graph.roots

def prepare (artifact : Artifact) (catalogue : GenericCatalogue.Checked artifact.sources)
    {owner name offset selector target}
    (table : QuantumArms.Table artifact.sources owner name offset selector target)
    (index : Fin table.arms.length) (implementations : List Request) (references : List (List Request)) :
    WorkM (Prepared artifact catalogue table index implementations references) := do
  -- Selecting the actual linked arm list and original caller row is charged;
  -- the graph/source/Meaning readers retain all their own byte work.
  exactWork (Exact.charge (16*(table.arms.length+owner.utf8ByteSize+1)))
  let arm := table.arms[index.val]'index.isLt
  let graph ← NaturalAffine.witness
    (RuntimePreparedOperation.prepareGraph artifact catalogue arm.operation.graph implementations references)
  let relevance ← SourceRows.read ([(owner,table.site.original.source)] ++ arm.sourceRows ++ graph.val.rows)
  return ⟨graph.val,by with_reducible exact graph.property,relevance⟩

inductive Variant where
  | plain | requested | constructed
  deriving BEq, DecidableEq, Repr

private def variant (description : OperationDescription.Description) : Variant :=
  match description.nodes with
  | [.provider ..] => .plain
  | [.provider ..,.requested ..] => .requested
  | _ => .constructed

inductive Checked {artifact catalogue owner name offset selector target table index implementations references}
    (prepared : @Prepared artifact catalogue owner name offset selector target table index implementations references)
    (root : Validity.Root) : Type where
  | plain (source : variant (table.arms[index.val]'index.isLt).operation.description = .plain)
      (actual : RuntimePreparedOperation.PlainChecked prepared.graph root OperationAccess.controllable)
      (original : RuntimeInterval.Computed
        (RuntimePreparedOperation.readPlain prepared.graph root OperationAccess.controllable) actual)
  | requested (source : variant (table.arms[index.val]'index.isLt).operation.description = .requested)
      (actual : RuntimePreparedOperation.GraphChecked prepared.graph root OperationAccess.controllable)
      (original : RuntimeInterval.Computed
        (RuntimePreparedOperation.readGraph prepared.graph root OperationAccess.controllable) actual)
  | constructed (source : variant (table.arms[index.val]'index.isLt).operation.description = .constructed)
      (actual : RuntimeOperationTree.Checked prepared.graph root OperationAccess.controllable)
      (original : RuntimeInterval.Computed
        (RuntimeOperationTree.read prepared.graph root OperationAccess.controllable) actual)
      (markers : RuntimeSourceOperationMarkers.Checked
        (table.arms[index.val]'index.isLt).operation prepared.graph actual)
      (markersRead : RuntimeInterval.Computed
        (RuntimeSourceOperationMarkers.read (table.arms[index.val]'index.isLt).operation prepared.graph actual) markers)

def Checked.action {artifact catalogue owner name offset selector target table index implementations references prepared root} :
    @Checked artifact catalogue owner name offset selector target table index implementations references prepared root → Semantics.Exact.Matrix
  | .plain _ actual _ => actual.subject.action
  | .requested _ actual _ => actual.subject.action
  | .constructed _ actual _ _ _ => actual.action

def Checked.demand {artifact catalogue owner name offset selector target table index implementations references prepared root} :
    @Checked artifact catalogue owner name offset selector target table index implementations references prepared root → StaticOperation.Paths
  | .plain _ actual _ => actual.demand
  | .requested _ actual _ => actual.demand
  | .constructed .. => OperationAccess.controllable

/-- Every arm requests the real controlled path. The occurrence checker must
materialize every demanded provider path; a Unit label or matching M matrix is
insufficient. Constructed source assertions retain the same checked equation,
complete original declaration and exact occurrence; complete catalogue-duty
association remains separate. Shapes choose one reader without retry. -/
def read {artifact catalogue owner name offset selector target table index implementations references}
    (prepared : @Prepared artifact catalogue owner name offset selector target table index implementations references)
    (root : Validity.Root) : WorkM (Checked prepared root) := do
  match source : variant (table.arms[index.val]'index.isLt).operation.description with
  | .plain =>
    let actual ← NaturalAffine.witness
      (RuntimePreparedOperation.readPlain prepared.graph root OperationAccess.controllable)
    return .plain source actual.val (by with_reducible exact actual.property)
  | .requested =>
    let actual ← NaturalAffine.witness
      (RuntimePreparedOperation.readGraph prepared.graph root OperationAccess.controllable)
    return .requested source actual.val (by with_reducible exact actual.property)
  | .constructed =>
    let actual ← NaturalAffine.witness
      (RuntimeOperationTree.read prepared.graph root OperationAccess.controllable)
    let markers ← NaturalAffine.witness
      (RuntimeSourceOperationMarkers.read (table.arms[index.val]'index.isLt).operation prepared.graph actual.val)
    return .constructed source actual.val (by with_reducible exact actual.property)
      markers.val (by with_reducible exact markers.property)

end QleisliKernel.Qirf.RuntimePreparedArm
