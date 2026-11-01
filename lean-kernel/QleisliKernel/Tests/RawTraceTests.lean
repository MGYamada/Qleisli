import QleisliKernel.Qirf.RawTrace
import QleisliKernel.Tests.SourceTraceOriginals

/-! Small original-source/Raw association controls, at most two physical bits.
The qmatch cases exercise structural intervals only; their separate arm equations
are deliberately not supplied here. No case authorizes execution.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RawTraceTests
open QleisliKernel.Qirf
open QleisliKernel.SourceTypes
open QleisliKernel QleisliKernel.Semantics QleisliKernel.Qirf.RawTrace

def sources (source : String) : SourceTypes.Sources :=
  #[("main",source)] ++ SourceTraceOriginals.bundled
def single (body : String) (effect : String := "unitary") : String :=
  "pub " ++ effect ++ " fn route(q:Q<Bit>)->Q<Bit>{" ++ body ++ "}"
def pair (body : String) : String :=
  "pub unitary fn route(a:Q<Bit>,b:Q<Bit>)->(Q<Bit>,Q<Bit>){" ++ body ++ "}"
def zeroPair (body : String) : String :=
  "pub unitary fn route(u:Q<Unit>,q:Q<Bit>)->(Q<Unit>,Q<Bit>){" ++ body ++ "}"

def positions {source owner name} (checked : SourceTrace.Checked source owner name)
    (counts : List Nat) : List Position :=
  ((checked.result.events.zip counts).foldl (fun (ranges,start) (event,count) =>
    (ranges ++ [⟨offset event,start,count⟩],start+count)) ([],0)).1

def checks (source : String) (program : Observation.Program) (counts : List Nat)
    (edit : List Position → List Position := id) (work : Nat := 2000000000) : Bool :=
  match (SourceTrace.read (sources source) "main" "route").run work with
  | (.error _,_) => false
  | (.ok original,left) =>
    ((check original [] program (edit (positions original counts))).run left).1.isOk

def oneH : Observation.Program :=
  ⟨[⟨10,[7],1⟩],[],[.pure (.gate .h 10 13)],[13],[],.unitary⟩
def twoH : Observation.Program :=
  {oneH with operations := [.pure (.gate .h 10 13),.pure (.gate .h 13 14)],outputs := [14]}
def pairedH : Observation.Program :=
  ⟨[⟨10,[7],1⟩,⟨11,[3],1⟩],[],
    [.pure (.gate .h 10 13),.pure (.gate .h 11 14)],[13,14],[],.unitary⟩
def zeroHeld : Observation.Program :=
  ⟨[⟨10,[],0⟩,⟨11,[3],1⟩],[],[.pure (.gate .h 11 14)],[10,14],[],.unitary⟩
def scalarZero : Observation.Program :=
  ⟨[⟨10,[],0⟩],[],[.pure (.applyUnitary 10 13 [⟨[],.monomial [] [0] [1]⟩])],[13],[],.unitary⟩
def scalarSource := "pub unitary fn route(u:Q<Unit>)->Q<Unit>{global_phase_eighth(u)}"
def twoUnitSource :=
  "pub unitary fn route(a:Q<Unit>,b:Q<Unit>)->(Q<Unit>,Q<Unit>){(a,global_phase_eighth(b))}"
def twoUnit : Observation.Program :=
  ⟨[⟨10,[],0⟩,⟨11,[],0⟩],[],
    [.pure (.applyUnitary 11 13 [⟨[],.monomial [] [0] [1]⟩])],[10,13],[],.unitary⟩
def selection := "qmatch(s,q){Tag::A=>keep,Tag::B=>keep}"
def matchSource (body : String) :=
  "pub enum Tag{A,B} unitary fn keep(q:Q<Bit>)->Q<Bit>{q}" ++
  "pub unitary fn route(s:Q<Tag>,q:Q<Bit>,u:Q<Unit>)->(Q<Unit>,Q<Tag>,Q<Bit>){" ++ body ++ "}"
def mixedProgram : Observation.Program :=
  ⟨[⟨0,[0],1⟩,⟨1,[1],1⟩,⟨2,[],0⟩],[],
    [.pure (.gate .h 1 3),.pure (.join 0 3 4),.pure (.split 4 5 6 1)],
    [2,5,6],[],.unitary⟩
def mixedSource := matchSource ("let q=h(q);let(s,q)=" ++ selection ++ ";(u,s,q)")

def controls : List (String × Bool) := [
  ("single original H binds the literal instruction",checks (single "h(q)") oneH [1]),
  ("H cannot bind X",!checks (single "h(q)")
    {oneH with operations := [.pure (.gate .x 10 13)]} [1]),
  ("nested calls bind postorder, not sorted byte offsets",checks (single "h(h(q))") twoH [1,1]),
  ("nested call offsets cannot be sorted by lexical position",!checks (single "h(h(q))") twoH [1,1]
    (fun ranges => match ranges with
      | [a,b] => [{a with offset := b.offset},{b with offset := a.offset}] | _ => ranges)),
  ("canceling calls cannot be omitted",!checks (single "h(h(q))")
    {oneH with operations := [],outputs := [10]} []),
  ("outer call cannot absorb both original calls",!checks (single "h(h(q))") twoH [2]),
  ("stale Raw owner generation refuses",!checks (single "h(h(q))")
    {twoH with operations := [.pure (.gate .h 10 13),.pure (.gate .h 10 14)]} [1,1]),
  ("the old opening-parenthesis coordinate refuses",!checks (single "h(q)") oneH [1]
    (List.map fun p => {p with offset := p.offset+1})),
  ("uncovered prefix refuses",!checks (single "h(q)") twoH [1]
    (List.map fun p => {p with start := 1})),
  ("uncovered suffix refuses",!checks (single "h(q)") twoH [1]),
  ("overlapping intervals refuse",!checks (single "h(h(q))") twoH [1,1]
    (List.map fun p => {p with start := 0})),
  ("repeated site offset refuses",!checks (single "h(h(q))") twoH [1,1]
    (fun ranges => ranges.map fun p => {p with offset := (ranges.head?.map (·.offset)).getD 0})),
  ("two tuple calls retain the first returned owner",checks (pair "(h(a),h(b))") pairedH [1,1]),
  ("equal-width owner substitution refuses",!checks (pair "(h(a),h(b))")
    {pairedH with operations := [.pure (.gate .h 11 13),.pure (.gate .h 10 14)]} [1,1]),
  ("source tuple return order binds Raw outputs",!checks (pair "(h(a),h(b))")
    {pairedH with outputs := [14,13]} [1,1]),
  ("held zero-width owner remains in the complete frame",checks (zeroPair "(u,h(q))") zeroHeld [1]),
  ("zero-width owner cannot be omitted from outputs",!checks (zeroPair "(u,h(q))")
    {zeroHeld with outputs := [14]} [1]),
  ("zero-width owner cannot be omitted from inputs",!checks (zeroPair "(u,h(q))")
    {zeroHeld with inputs := [⟨11,[3],1⟩],outputs := [14]} [1]),
  ("scalar eighth phase on Unit retains its actual owner",checks scalarSource scalarZero [1]),
  ("wrong scalar phase refuses",!checks scalarSource
    {scalarZero with operations := [.pure (.applyUnitary 10 13 [⟨[],.monomial [] [0] [7]⟩])]} [1]),
  ("same-width-free source Unit cannot bind a bit port",!checks scalarSource
    {scalarZero with inputs := [⟨10,[7],1⟩]} [1]),
  ("two Unit owners retain distinct scalar target identity",checks twoUnitSource twoUnit [1]),
  ("identical empty wires cannot choose the other Unit owner",!checks twoUnitSource
    {twoUnit with
      operations := [.pure (.applyUnitary 10 13 [⟨[],.monomial [] [0] [1]⟩])]
      outputs := [13,11]} [1]),
  ("two Unit returns cannot be exchanged",!checks twoUnitSource {twoUnit with outputs := [13,10]} [1]),
  ("public Observe label stays Observe",checks (single "h(q)" "observe") {oneH with effect := .observe} [1]),
  ("public Observe cannot sharpen to Unitary",!checks (single "h(q)" "observe") oneH [1]),
  ("public Isometry label stays Isometry",checks (single "h(q)" "isometry") {oneH with effect := .isometry} [1]),
  ("public Unitary cannot hide observing root",!checks (single "h(q)") {oneH with effect := .observe} [1]),
  ("actual hidden observation refuses",!checks (single "h(q)" "observe")
    {oneH with operations := [.measure 10 0],outputs := [],classicalOutputs := [0],effect := .observe} [1]),
  ("identity source still receives the complete Raw root check",checks (single "q")
    {oneH with operations := [],outputs := [10]} []),
  ("identity cannot conceal an actual gate",!checks (single "q") oneH []),
  ("empty event stream still rejects invalid Raw ownership",!checks (single "q")
    {oneH with operations := [],outputs := [10,10]} []),
  ("primitive-name local shadow refuses",!checks
    "pub unitary fn route(h:Q<Bit>)->Q<Bit>{h(h)}" oneH [1]),
  ("ordinary named function is not primitive fallback",!checks
    ("unitary fn h(q:Q<Bit>)->Q<Bit>{q}" ++ single "h(q)") oneH [1]),
  ("primitive followed by structural qmatch interval",checks mixedSource mixedProgram [1,2]),
  ("qmatch interval cannot absorb the preceding primitive",!checks mixedSource mixedProgram [0,3]),
  ("qmatch boundary cannot cut a joined owner",!checks mixedSource mixedProgram [2,1]),
  ("complete wrong qmatch action still needs separate arm equation",
    checks (matchSource ("let(s,q)=" ++ selection ++ ";(u,s,q)")) mixedProgram [3]),
  ("empty work budget refuses",!checks (single "h(q)") oneH [1] id 0)
]

#guard controls.all (·.2)

#print axioms QleisliKernel.Qirf.RawTrace.check
#print axioms QleisliKernel.Qirf.RawTrace.Checked.everyOriginalEvent
#print axioms QleisliKernel.Qirf.RawTrace.Checked.completeOperations

end QleisliKernel.Tests.RawTraceTests
