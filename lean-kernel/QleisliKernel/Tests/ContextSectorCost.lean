import QleisliKernel.Tests.ContextSectorData

/-! Stage costs for the same small contextual controls. The first main/IR and
incomplete prelude proposal remain in ContextSectorData and Git history.
The current isolated empty-prelude environment is not a bundled-stdlib check.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.ContextSectorCost
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite
open QleisliKernel.Tests.ContextSectorTests
open ContextSector

def note {α : Type} (label : String) (before : Nat) (run : Except Finite.Error α × Nat) :
    String × Nat × Nat × Option Finite.Error :=
  (label,before-run.2,run.2,match run.1 with | .error error => some error | .ok _ => none)

def stages : List (String × Nat × Nat × Option Finite.Error) :=
  let first := (readHeaders artifact "main" "route" requests).run 10000000
  let firstNote := note "source and all original headers" 10000000 first
  match first.1 with
  | .error _ => [firstNote]
  | .ok headers =>
    let second := (prepare order headers positions).run first.2
    let secondNote := note "fresh graph and complete Raw context" first.2 second
    match second.1 with
    | .error _ => [firstNote,secondNote]
    | .ok body =>
      let selected := (collect body.context.val.sites).run second.2
      let selectedNote := note "actual selection sites" second.2 selected
      match selected.1 with
      | .error _ => [firstNote,secondNote,selectedNote]
      | .ok sites =>
        ((headers.sites.zip sites).zipIdx.foldl (fun (left,halted,notes) (pair,index) =>
          if halted then (left,halted,notes)
          else
            let next := (readLocal body pair).run left
            (next.2,!next.1.isOk,notes ++ [note s!"selection equations {index}" left next]))
          (selected.2,false,[firstNote,secondNote,selectedNote])).2.2

-- All five stages must actually finish under ONE unchanged 10M allowance.
-- Exact observed remainders are diagnostic history, not a semantic contract.
#guard stages.length = 5
#guard stages.all (fun stage => stage.2.2.2.isNone)
end QleisliKernel.Tests.ContextSectorCost
