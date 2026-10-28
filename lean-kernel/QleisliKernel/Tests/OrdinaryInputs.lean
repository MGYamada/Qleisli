import QleisliKernel.Qirf.OrdinaryFamily

/-! Small actual-definition input/history controls. These tests do not prove
source/runtime preservation. Copyright 2026 Qleisli Project Contributors. Apache-2.0. -/
namespace QleisliKernel.Tests.OrdinaryInputs

open QleisliKernel QleisliKernel.Qirf QleisliKernel.Qirf.OrdinaryFamily
open QleisliKernel.Semantics.FiniteCarrier QleisliKernel.Semantics.OrdinaryValue
open QleisliKernel.Semantics.Observation

def text : String := "enum Tri {A,B,C} pub fn f(value:Tri)->Tri {value}"
def origin (source : String := text) : Origin := ⟨"main","Tri",source⟩
def tri (source : String := text) : Basis := [.enumeration (origin source) ["A","B","C"]]
def identityProgram : Program := ⟨[],[0,1],[],[],[0,1],.unitary⟩
def artifact (program : Program := identityProgram) (source : String := text) : Artifact :=
  ⟨#[program],#[],#[("main",source)],0,none⟩
def request (source : String := text) : Request :=
  ⟨.exported,"main","f",[tri source],[.enumeration (origin source) [0,1]],
    [[false,false],[true,false],[false,true]],
    tri source,.enumeration (origin source) [0,1],.unitary⟩

def ordinal : Value → Nat
  | .enumeration _ value => value
  | _ => 999

def summaries {root request} : Nat → ({assignments : List (List Bool)} →
    Rows root request assignments → List (List Nat)) :=
  Nat.rec (fun {_} _ => []) (fun _ next {_} rows =>
    match rows with
    | .nil => []
    | .cons head tail => head.outputs.items.map ordinal :: next tail)

def observe (actual : Artifact) (requested : Request) : Option (List Nat × List (List Nat)) :=
  match (OrdinaryFamily.check actual #[0] requested).run 10000000 with
  | (.ok checked,_) => some (checked.domain.code.labels,
      summaries (checked.domain.code.labels.length+1) checked.rows)
  | _ => none

def lateInvalid : Program :=
  ⟨[],[0,1],[.branch 1 [.constant true 2,.constant true 3] [] []
    [⟨2,0,4⟩,⟨3,1,5⟩]],[],[4,5],.unitary⟩

def observingText : String := "enum Tri {A,B,C} pub observe fn f(value:Tri)->Tri {value}"
def observingProgram (invalid : Bool := false) : Program :=
  ⟨[],[0,1],[.pure (.init0 0 0),.measure 0 2,.constant false 3],[],
    if invalid then [2,2] else [2,3],.observe⟩
def observingRequest (source : String := observingText) (invalid : Bool := false) : Request :=
  {request source with
    storage := .enumeration (origin source) (if invalid then [2,2] else [2,3])
    publicEffect := .observe}

def unitText : String := "enum Tri {A,B,C} pub fn f(empty:Unit,value:Tri)->Tri {value}"
def unitRequest : Request :=
  {request unitText with
    inputs := [[.unit],tri unitText]
    inputStorage := [.unit,.enumeration (origin unitText) [0,1]]}

def controls : List (String × Bool) := [
  ("all three canonical inputs keep original codes",observe (artifact) (request) ==
    some ([0,1,2],[[0],[1],[2]])),
  ("invalid result only on the last canonical input refuses",
    (observe (artifact lateInvalid) {request with storage := .enumeration (origin) [4,5]}).isNone),
  ("actual input order is exact",
    (observe (artifact) {request with inputStorage := [.enumeration (origin) [1,0]]}).isNone),
  ("actual output order is exact",
    (observe (artifact) {request with storage := .enumeration (origin) [1,0]}).isNone),
  ("original input type cannot be replaced by equal-width bits",
    (observe (artifact) {request with inputs := [[.bits 2]]}).isNone),
  ("original result type cannot be replaced by equal-width bits",
    (observe (artifact) {request with basis := [.bits 2]}).isNone),
  ("explicit zero-width argument is retained",observe (artifact identityProgram unitText) unitRequest ==
    some ([0,1,2],[[0],[1],[2]])),
  ("erasing zero-width input storage refuses",
    (observe (artifact identityProgram unitText)
      {unitRequest with inputStorage := [.enumeration (origin unitText) [0,1]]}).isNone),
  ("all hidden histories including zero-probability outcomes remain typed",
    observe (artifact (observingProgram) observingText) (observingRequest) ==
      some ([0,1,2],[[0,1],[0,1],[0,1]])),
  ("invalid zero-probability hidden result refuses",
    (observe (artifact (observingProgram true) observingText) (observingRequest observingText true)).isNone),
  ("observation cannot be relabelled Unitary",
    (observe (artifact (observingProgram) observingText)
      {observingRequest with publicEffect := .unitary}).isNone),
  ("producer row subset is refused",
    (observe (artifact) {request with inputRows := [[false,false],[true,false]]}).isNone),
  ("producer row permutation is refused",
    (observe (artifact) {request with inputRows := [[true,false],[false,false],[false,true]]}).isNone),
  ("producer padding input is refused",
    (observe (artifact) {request with inputRows := [[false,false],[true,false],[true,true]]}).isNone),
  ("producer duplicate input is refused",
    (observe (artifact) {request with inputRows := [[false,false],[true,false],[true,false]]}).isNone),
  ("producer wrong row width is refused",
    (observe (artifact) {request with inputRows := [[false],[true],[false]]}).isNone),
  ("private parameter declaration retains Internal selection",
    let source := "enum Tri {A,B,C} fn f(value:Tri)->Tri {value}"
    observe (artifact identityProgram source) {request source with selection := .internal} ==
      some ([0,1,2],[[0],[1],[2]])),
  ("exported selection cannot expose a private parameter declaration",
    let source := "enum Tri {A,B,C} fn f(value:Tri)->Tri {value}"
    (observe (artifact identityProgram source) (request source)).isNone),
  ("Internal selection refuses a public parameter declaration",
    (observe (artifact) {request with selection := .internal}).isNone),
  ("exhausted work is a refusal",
    match (OrdinaryFamily.check (artifact) #[0] (request)).run 0 with
    | (.error _,_) => true | _ => false)]

-- These are finite executable-definition regressions, not a general theorem
-- about source lowering, runtime execution or arbitrary quantum inputs.
example : controls.length = 20 := by decide

end QleisliKernel.Tests.OrdinaryInputs
