import QleisliKernel.Qirf.SourceBodyContext

/-! One fresh graph for the selected source and every original arm body.
Source discovery precedes graph acceptance; checking a child never substitutes
a second root, stale receipt, reconstructed source or replacement dependency.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SourceBodyGraph
open QleisliKernel QleisliKernel.SourceTypes QleisliKernel.Qirf Finite
open PureInterval (Witness)
abbrev Context := SourceContextRequest.Context

structure Headers (artifact : Artifact) (owner name : String)
    (arguments : StaticTypes.Arguments) (request : Context) where
  signature : Witness (QuantumSignature.readWithArguments artifact.sources owner name arguments)
  source : Witness (SourceTrace.readWithSignature signature.val)
  header : SourceBodyHeader.Header source.val.checked request
  discovery : Witness (SourceBodyHeader.discover artifact 128 header)

def readHeaders (artifact : Artifact) (owner name : String)
    (arguments : StaticTypes.Arguments) (request : Context) :
    WorkM (Headers artifact owner name arguments request) := do
  let signature ← NaturalAffine.witness (QuantumSignature.readWithArguments artifact.sources owner name arguments)
  let source ← NaturalAffine.witness (SourceTrace.readWithSignature signature.val)
  let header ← SourceBodyHeader.read source.val.checked request
  let discovery ← NaturalAffine.witness (SourceBodyHeader.discover artifact 128 header)
  return ⟨signature,source,header,discovery⟩

def rows {artifact owner name arguments request}
    (headers : Headers artifact owner name arguments request) : List (String × String) :=
  SourceBodyHeader.rows headers.header ++
    headers.discovery.val.arms.flatMap (fun arm => SourceBodyHeader.rows arm.header) ++
    headers.discovery.val.calls.flatMap (fun call => SourceBodyHeader.rows call.header)

def roots {artifact owner name arguments request}
    (headers : Headers artifact owner name arguments request) : List Nat :=
  (artifact.root :: SourceBodyHeader.roots headers.header ++
    headers.discovery.val.arms.flatMap (fun arm => SourceBodyHeader.roots arm.header) ++
    headers.discovery.val.calls.flatMap (fun call => SourceBodyHeader.roots call.header)).eraseDups

structure Body {artifact owner name arguments request} (order : Array Nat)
    (headers : Headers artifact owner name arguments request) where
  root : Witness (Validity.checkRootFromRoots artifact order (rows headers) (roots headers))
  context : SourceBodyContext.Checked headers.header root.val (SelectionContract.rootFresh root) root.val.program
  arms : Witness (headers.discovery.val.arms.mapM fun arm => do
    let body ← SourceBodyContext.checkArm root arm
    return (⟨arm,body⟩ : (arm : SourceBodyHeader.Arm artifact) × SourceBodyContext.ArmChecked root arm))

def prepare {artifact owner name arguments request} (order : Array Nat)
    (headers : Headers artifact owner name arguments request) : WorkM (Body order headers) := do
  let bytes := (artifact.sources.toList.map fun row => row.1.utf8ByteSize+row.2.utf8ByteSize).sum
  let rowCount := (rows headers).length
  let rootCount := 1+(SourceBodyHeader.roots headers.header).length+
    (headers.discovery.val.arms.map fun arm => (SourceBodyHeader.roots arm.header).length).sum+
    (headers.discovery.val.calls.map fun call => (SourceBodyHeader.roots call.header).length).sum
  exactWork (Exact.charge (5+(bytes+artifact.sources.size+1)*(rowCount+1)+16*rootCount^2))
  let root ← NaturalAffine.witness (Validity.checkRootFromRoots artifact order (rows headers) (roots headers))
  let context ← SourceBodyContext.check headers.header root.val (SelectionContract.rootFresh root) root.val.program
  let arms ← NaturalAffine.witness (headers.discovery.val.arms.mapM fun arm => do
    let body ← SourceBodyContext.checkArm root arm
    return (⟨arm,body⟩ : (arm : SourceBodyHeader.Arm artifact) × SourceBodyContext.ArmChecked root arm))
  return ⟨root,context,arms⟩

structure Checked (artifact : Artifact) (order : Array Nat) (owner name : String)
    (arguments : StaticTypes.Arguments) (request : Context) where
  headers : Headers artifact owner name arguments request
  body : Body order headers

def check (artifact : Artifact) (order : Array Nat) (owner name : String)
    (arguments : StaticTypes.Arguments) (request : Context) :
    WorkM (Checked artifact order owner name arguments request) := do
  let headers ← readHeaders artifact owner name arguments request
  let body ← prepare order headers
  return ⟨headers,body⟩

theorem Checked.originalRoot {artifact order owner name arguments request}
    (checked : Checked artifact order owner name arguments request) :
    ∃ work, Validity.SourceRootPostconditionFromRoots artifact order (rows checked.headers)
      (roots checked.headers) checked.body.root.val work := by
  obtain ⟨work,left,ran⟩ := checked.body.root.property
  exact ⟨work,Validity.checkRootFromRoots_postcondition _ _ _ _ _ _ _ ran⟩

theorem Checked.allOriginalEvents {artifact order owner name arguments request}
    (checked : Checked artifact order owner name arguments request) :
    request.positions.map (·.offset) = checked.headers.source.val.checked.result.events.map RawTrace.offset :=
  checked.body.context.trace.val.everyOriginalEvent

end QleisliKernel.Qirf.SourceBodyGraph
