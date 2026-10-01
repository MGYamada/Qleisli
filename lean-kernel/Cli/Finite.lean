import Cli.Common

/-! Unproved transport adapter for the existing experimental profiles.
Inputs remain untrusted until checked by the independently specified pure kernel.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.Cli
open Internal

def run (artifactPath requirementPath : String) : IO UInt32 := do
  let artifact ← readParsed artifactPath Protocol.parseArtifact .artifact (emit false)
  let some artifact := artifact | return 1
  let requirement ← readParsed requirementPath Protocol.parseRequirement .requirement (emit false)
  let some requirement := requirement | return 1
  let accepted := verify artifact.word artifact.claimed requirement
  emit accepted (if accepted then .accepted else .rejected) .verification
  return if accepted then 0 else 1

private def emitDag (accepted : Bool) (code : String) (stage : Stage)
    (failureNode : Option Nat := none) (stats : Option Hierarchy.Stats := none) : IO Unit := do
  let node := match failureNode with
    | none => "null"
    | some value => toString value
  let metrics := match stats with
    | none => "null"
    | some value =>
      "{\"nodes\":" ++ toString value.nodes ++
      ",\"references\":" ++ toString value.references ++
      ",\"work_units\":" ++ toString value.workUnits ++
      ",\"depth\":" ++ toString value.depth ++
      ",\"expanded_gates\":" ++ toString value.expandedGates ++
      ",\"dense_dimension\":0}"
  emitResult "phase256-dag-v1" accepted code stage
    (",\"node\":" ++ node ++ ",\"stats\":" ++ metrics)

def runDag (artifactPath requirementPath : String) : IO UInt32 := do
  let artifact ← readParsed artifactPath Protocol.Dag.parseArtifact .artifact (fun code stage => emitDag false (codeName code) stage)
  let some artifact := artifact | return 1
  let requirement ← readParsed requirementPath Protocol.Dag.parseRequirement .requirement (fun code stage => emitDag false (codeName code) stage)
  let some requirement := requirement | return 1
  match Hierarchy.check artifact.definitions artifact.entry requirement with
  | .ok stats =>
    emitDag true "accepted" .verification none (some stats)
    return 0
  | .error failure =>
    let code := match failure.kind with
      | .invalidIr => "invalid_ir"
      | .contract => "contract"
      | .limit => "limit"
    emitDag false code .verification (some failure.node)
    return 1

private def emitLayout (accepted : Bool) (code : String) (stage : Stage)
    (stats : Option Layout.Stats := none) : IO Unit := do
  let metrics := match stats with
    | none => "null"
    | some value =>
      "{\"owners\":" ++ toString value.owners ++
      ",\"axes\":" ++ toString value.axes ++
      ",\"type_atoms\":" ++ toString value.typeAtoms ++
      ",\"work_units\":" ++ toString value.workUnits ++ ",\"dense_dimension\":0}"
  emitResult "typed-layout-v1" accepted code stage
    (",\"stats\":" ++ metrics)

def runLayout (artifactPath requirementPath : String) : IO UInt32 := do
  let artifact ← readParsed artifactPath Protocol.Layout.parseArtifact .artifact (fun code stage => emitLayout false (codeName code) stage)
  let some artifact := artifact | return 1
  let requirement ← readParsed requirementPath Protocol.Layout.parseRequirement .requirement (fun code stage => emitLayout false (codeName code) stage)
  let some requirement := requirement | return 1
  match Layout.check artifact.layout artifact.witness requirement with
  | .ok stats =>
    emitLayout true "accepted" .verification (some stats)
    return 0
  | .error failure =>
    let code := match failure with
      | .invalidIr => "invalid_ir"
      | .contract => "contract"
      | .limit => "limit"
    emitLayout false code .verification
    return 1

private def emitLayoutDag (accepted : Bool) (code : String) (stage : Stage)
    (node : Option Nat := none) (stats : Option LayoutDag.Stats := none) : IO Unit := do
  let node := match node with | none => "null" | some value => toString value
  let metrics := match stats with
    | none => "null"
    | some value =>
      "{\"nodes\":" ++ toString value.nodes ++
      ",\"references\":" ++ toString value.references ++
      ",\"work_units\":" ++ toString value.workUnits ++
      ",\"depth\":" ++ toString value.depth ++
      ",\"expanded_layouts\":" ++ toString value.expandedLayouts ++
      ",\"dense_dimension\":0}"
  emitResult "typed-layout-dag-v1" accepted code stage
    (",\"node\":" ++ node ++ ",\"stats\":" ++ metrics)

def runLayoutDag (artifactPath requirementPath : String) : IO UInt32 := do
  let artifact ← readParsed artifactPath Protocol.LayoutDag.parseArtifact .artifact (fun code stage => emitLayoutDag false (codeName code) stage)
  let some artifact := artifact | return 1
  let requirement ← readParsed requirementPath Protocol.Layout.parseRequirement .requirement (fun code stage => emitLayoutDag false (codeName code) stage)
  let some requirement := requirement | return 1
  match LayoutDag.check artifact.definitions artifact.entry requirement with
  | .ok stats =>
    emitLayoutDag true "accepted" .verification none (some stats)
    return 0
  | .error failure =>
    let code := match failure.kind with
      | .invalidIr => "invalid_ir"
      | .contract => "contract"
      | .limit => "limit"
    emitLayoutDag false code .verification (some failure.node)
    return 1

def usage : IO UInt32 := do
  emit false .usage .usage
  return 2

private def emitPhaseLayout (accepted : Bool) (code : String) (stage : Stage)
    (node : Option Nat := none) (stats : Option PhaseLayout.Stats := none) : IO Unit := do
  let node := match node with | none => "null" | some value => toString value
  let metrics := match stats with
    | none => "null"
    | some value =>
      "{\"nodes\":" ++ toString value.layout.nodes ++
      ",\"references\":" ++ toString value.layout.references ++
      ",\"work_units\":" ++ toString (value.layout.workUnits + value.phaseWork) ++
      ",\"phase_work_units\":" ++ toString value.phaseWork ++
      ",\"depth\":" ++ toString value.layout.depth ++
      ",\"expanded_layouts\":" ++ toString value.layout.expandedLayouts ++
      ",\"expanded_phase_terms\":" ++ toString value.expandedPhaseTerms ++
      ",\"terms\":" ++ toString value.terms ++ ",\"dense_dimension\":0}"
  emitResult "typed-phase256-dag-v1" accepted code stage
    (",\"node\":" ++ node ++ ",\"stats\":" ++ metrics)

def runPhaseLayout (artifactPath requirementPath : String) : IO UInt32 := do
  let artifact ← readParsed artifactPath Protocol.PhaseLayout.parseArtifact .artifact (fun code stage => emitPhaseLayout false (codeName code) stage)
  let some artifact := artifact | return 1
  let requirement ← readParsed requirementPath Protocol.PhaseLayout.parseRequirement .requirement (fun code stage => emitPhaseLayout false (codeName code) stage)
  let some requirement := requirement | return 1
  match PhaseLayout.check artifact.definitions artifact.entry requirement with
  | .ok stats =>
    emitPhaseLayout true "accepted" .verification none (some stats)
    return 0
  | .error failure =>
    let code := match failure.kind with
      | .invalidIr => "invalid_ir"
      | .contract => "contract"
      | .limit => "limit"
    emitPhaseLayout false code .verification (some failure.node)
    return 1

end QleisliKernel.Cli
