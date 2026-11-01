import QleisliKernel.Qirf.ContextSector
import QleisliKernel.Tests.SourceTraceOriginals
import QleisliKernel.SourceTypes.Lexer

/-! Informed two-qubit controls, not independent authoring or a general proof.
A prefix and suffix H surround two cancelling controlled-Z selections.
Each original selection still needs its own arm/control/sector equations.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.ContextSectorCost
open QleisliKernel.Qirf
open QleisliKernel.SourceTypes
open QleisliKernel QleisliKernel.Semantics
open Semantics.Raw Semantics.FiniteCarrier Semantics.CarrierInterface
open ContextSector

def selection := "qmatch(s,q){Tag::B=>sign,Tag::A=>keep}"
def text := "// λ qmatch is not a comment site\npub enum Tag{A,B} " ++
  "unitary fn keep(q:Q<Bit>)->Q<Bit>{q} unitary fn sign(q:Q<Bit>)->Q<Bit>{phase[1,1](q)} " ++
  "pub unitary fn route(s:Q<Tag>,q:Q<Bit>,u:Q<Unit>)->(Q<Unit>,Q<Tag>,Q<Bit>){" ++
  "let q=h(q);let(s,q)=" ++ selection ++ ";let(s,q)=" ++ selection ++ ";(u,s,h(q))}"
def tag : Basis := [.enumeration ⟨"main","Tag",text⟩ ["A","B"]]
def offsets := SourceTypes.QuantumSequence.originalOffsets ((SourceTypes.lexLocated text).toOption.getD [])
def phaseStep (phase : Nat) : Semantics.Finite.Step := ⟨[⟨0,true⟩],.monomial [1] [0,1] [0,phase]⟩

def main (first second : Nat := 4) : Observation.Program :=
  ⟨[⟨0,[0],1⟩,⟨1,[1],1⟩,⟨2,[],0⟩],[],
    [.pure (.gate .h 1 3),
      .pure (.join 0 3 4),.pure (.applyUnitary 4 5 [phaseStep first]),.pure (.split 5 6 7 1),
      .pure (.join 6 7 8),.pure (.applyUnitary 8 9 [phaseStep second]),.pure (.split 9 10 11 1),
      .pure (.gate .h 11 12)],
    [2,10,12],[],.unitary⟩
def arm (phase : Nat) : Observation.Program :=
  ⟨[⟨10,[7],1⟩],[],[.pure (.applyUnitary 10 11 [⟨[],.monomial [0] [0,1] [0,phase]⟩])],[11],[],.unitary⟩
def controlled (phase : Nat) : Observation.Program :=
  ⟨[⟨10,[7],1⟩,⟨11,[91],1⟩],[],[.pure (.join 10 11 12),
    .pure (.applyUnitary 12 13 [phaseStep phase]),.pure (.split 13 14 15 1)],[14,15],[],.unitary⟩
def prelude : String :=
  ((SourceTraceOriginals.bundled.toList.find? fun row => row.1 == "std::prelude").map (·.2)).getD ""

def artifact : Qirf.Artifact :=
  ⟨#[main,arm 0,controlled 0,arm 4,controlled 4],
    #[⟨[.bit],1,.phase8 [0,0],"main::keep","independent::identity",[0]⟩,
      ⟨[.bit],3,.phase8 [0,4],"main::sign","independent::z",[0]⟩],#[("main",text),("std::prelude",prelude)],0,none⟩
def order : Array Nat := #[1,2,3,4,5,6,0]

def interface (second : Bool) : Interface :=
  ⟨[⟨⟨if second then 6 else 0,[0],1⟩,tag⟩,⟨⟨if second then 7 else 3,[1],1⟩,[.bit]⟩],
    [⟨⟨if second then 10 else 6,[0],1⟩,tag⟩,⟨⟨if second then 11 else 7,[1],1⟩,[.bit]⟩],.unitary⟩
def firstRequest : Request :=
  ⟨interface false,interface false,⟨offsets[0]?.getD 0,1,3⟩,[⟨1,4⟩,⟨0,2⟩]⟩
def secondRequest : Request :=
  ⟨interface true,interface true,⟨offsets[1]?.getD 0,4,3⟩,[⟨1,4⟩,⟨0,2⟩]⟩
def requests : List Request := [firstRequest,secondRequest]

/-- Original source-derived offsets, with untrusted literal interval proposals.
The complete checker independently rereads both sources and intervals. -/
def positions : List Position :=
  match (SourceTrace.read artifact.sources "main" "route").run 10000000 with
  | (.ok source,_) =>
      ((source.result.events.map QleisliKernel.Qirf.RawTrace.offset).zip [(0,1),(1,3),(4,3),(7,1)]).map
        fun (offset,start,count) => ⟨offset,start,count⟩
  | _ => []

def result (data : Qirf.Artifact := artifact) (asked : List Request := requests)
    (placed : List Position := positions) (work : Nat := 10000000) : Except Finite.Error (List Nat) :=
  ((ContextSector.check data order "main" "route" placed asked).run work).1.map fun checked =>
    checked.locals.map (·.checked.equations.logical.length)
def failure (data : Qirf.Artifact := artifact) (asked : List Request := requests)
    (placed : List Position := positions) : Option Finite.Error :=
  match result data asked placed with | .error error => some error | .ok _ => none

def wrongPrefix : Observation.Program :=
  {main with operations := (main.operations.modify 0 (fun _ =>
    .pure (.applyUnitary 1 3 [⟨[],.monomial [0] [0,1] [0,4]⟩])))}
def wrongSuffix : Observation.Program :=
  {main with operations := (main.operations.modify 7 (fun _ =>
    .pure (.applyUnitary 11 12 [⟨[],.monomial [0] [0,1] [0,4]⟩])))}
def budgetFailure (work : Nat) : Option Finite.Error :=
  match result artifact requests positions work with
  | .error error => some error
  | .ok _ => none

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

-- Exact observations from the retained two-bit experiment, with one shared budget.
#guard stages = [
  ("source and all original headers",4568552,5431448,none),
  ("fresh graph and complete Raw context",4547461,883987,none),
  ("actual selection sites",5,883982,none),
  ("selection equations 0",179942,704040,none),
  ("selection equations 1",180454,523586,none)]
end QleisliKernel.Tests.ContextSectorCost
