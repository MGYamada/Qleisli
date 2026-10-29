import QleisliKernel.Semantics.Raw
import QleisliKernel.Semantics.SourceOwners

/-! Logical source-owner transport through an original pure Raw subject.
This reference imports no checker. A source quantum owner is an opaque leaf;
explicit Raw joins retain their ordered pair, and a split recovers that pair.
Widths constrain a split but cannot identify an owner, including at width zero.
This is a structural transport relation, not a replacement Raw meaning, a
general source-lowering theorem or a new constitutional guarantee. Raw encodings
that split an opaque source owner need a separate checked typed refinement.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Semantics.RawOwnerFlow
open SourceOwners Raw

inductive Tree where
  | owner (value : SourceOwners.Owner) (bits : Nat)
  | pair (left right : Tree) (bits : Nat)

/-- The run seeds widths from actual Raw input ports; its only pair constructor
stores the sum of its actual children. No proposed tree/cache enters the run.
Original source/code typing is checked by the enclosing typed interface gate. -/
def Tree.width : Tree → Nat
  | .owner _ bits | .pair _ _ bits => bits

abbrev Frame := List (Nat × Tree)

/-- Removing a token transfers the entire logical tree. No wire comparison
or arbitrary selection between equal-width owners contributes to this move. -/
def take (token : Nat) (frame : Frame) : Option (Tree × Frame) :=
  (frame.foldr (fun cell (rest,result) =>
    (cell :: rest,if cell.1 == token then some (cell.2,rest)
      else result.map fun (tree,remaining) => (tree,cell :: remaining))) ([],none)).2

def put (token : Nat) (tree : Tree) (frame : Frame) : Option Frame :=
  if frame.any (fun cell => cell.1 == token) then none else some ((token,tree) :: frame)

def move (input output : Nat) (frame : Frame) : Option Frame := do
  let (tree,remaining) ← take input frame
  put output tree remaining

def moveMany (targets : List Target) (frame : Frame) : Option Frame := do
  let (values,remaining) ← targets.foldlM (fun (values,current) target => do
    let (tree,after) ← take target.input current
    return ((target.output,tree) :: values,after)) ([],frame)
  values.foldlM (fun current cell => put cell.1 cell.2 current) remaining

/-- These are literal original operations, not a producer's provenance table.
Allocation/release and splitting an atomic source owner need their source rules
or an independently checked representation refinement before use here. -/
def step (frame : Frame) : Op → Option Frame
  | .gate _ input output | .applyUnitary input output _
  | .certifiedCompute input output _ _ _ _ =>
    move input output frame
  | .liftBasis input output wires _ => do
    let (tree,remaining) ← take input frame
    if tree.width != wires.length then none else put output tree remaining
  | .cnot control target controlOut targetOut
  | .quantumIf control target controlOut targetOut _ _ =>
    moveMany [⟨control,controlOut⟩,⟨target,targetOut⟩] frame
  | .toffoli a b target aOut bOut targetOut =>
    moveMany [⟨a,aOut⟩,⟨b,bOut⟩,⟨target,targetOut⟩] frame
  | .computeUseUncompute input output targets _ _ _ =>
    moveMany (⟨input,output⟩ :: targets) frame
  | .join left right output => do
    let (a,afterLeft) ← take left frame
    let (b,remaining) ← take right afterLeft
    put output (.pair a b (a.width+b.width)) remaining
  | .split input left right leftBits => do
    let (.pair a b _,remaining) ← take input frame | none
    if a.width != leftBits then none else do
      let afterLeft ← put left a remaining
      put right b afterLeft
  | .init0 _ _ | .packUnit _ | .unpackUnit _ => none

def seed (owners : List SourceOwners.Owner) (inputs : List Port) : Option Frame := do
  if owners.length != inputs.length then none else
  (owners.zip inputs).foldlM (fun frame (owner,port) => do
    put port.token (.owner owner port.bits) frame) []

def returned (outputs : List Nat) (frame : Frame) : Option (List SourceOwners.Owner) := do
  let (values,remaining) ← outputs.foldlM (fun (values,current) token => do
    let (.owner owner _,after) ← take token current | none
    return (owner :: values,after)) ([],frame)
  if !remaining.isEmpty then none else some values.reverse

def run (owners : List SourceOwners.Owner) (program : Program) : Option (List SourceOwners.Owner) := do
  let initial ← seed owners program.inputs
  let final ← program.operations.foldlM step initial
  returned program.outputs final

/-- Exact original-operation transport of complete ordered source owners.
The independent Raw validity/effect and operator equations remain separate. -/
def Returns (inputs : List SourceOwners.Owner) (program : Program)
    (outputs : List SourceOwners.Owner) : Prop := run inputs program = some outputs

end QleisliKernel.Semantics.RawOwnerFlow
