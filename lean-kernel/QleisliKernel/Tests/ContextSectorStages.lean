import QleisliKernel.Tests.ContextSectorData

/-! Diagnostic stages for the preserved small contextual regression.
All observations use the unchanged ten-million-work budget. This executable
probe records actual errors/work; it changes no expected result or limit.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.ContextSectorStages
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite QleisliKernel.SourceTypes
open ContextSectorTests

private def snapshot {α : Type} (action : WorkM α) (project : α → Nat) : Except Error Nat × Nat :=
  let (result,remaining) := action.run 10000000
  (result.map project,remaining)

def source := snapshot (SourceTrace.read artifact.sources "main" "route") (fun checked => checked.result.events.length)
def headers := snapshot (ContextSector.readHeaders artifact "main" "route" requests) (fun checked => checked.sites.length)
def graph := snapshot (do
  let checked ← ContextSector.readHeaders artifact "main" "route" requests
  let graph ← ContextSector.prepare order checked positions
  return graph.root.val.program.operations.length) id

def complete := snapshot (ContextSector.check artifact order "main" "route" positions requests)
  (fun checked => checked.locals.length)

def mutations : List (String × Qirf.Artifact) := [
  ("correct",artifact),
  ("first-sector-phase",{artifact with programs := artifact.programs.set! 0 (main 2 4)}),
  ("second-sector-phase",{artifact with programs := artifact.programs.set! 0 (main 4 2)}),
  ("cancelled-wrong-sectors",{artifact with programs := artifact.programs.set! 0 (main 0 0)}),
  ("arm-phase",{artifact with programs := artifact.programs.set! 3 (arm 2)}),
  ("control-phase",{artifact with programs := artifact.programs.set! 4 (controlled 2)})]

def outcomes := mutations.map fun (label,data) =>
  (label,snapshot (ContextSector.check data order "main" "route" positions requests)
    (fun checked => checked.locals.length))

#eval source
#eval (positions.length,offsets.length)
#eval headers
#eval graph
#eval complete
#eval outcomes
#eval controls.filter (fun control => !control.2) |>.map (·.1)

end QleisliKernel.Tests.ContextSectorStages
