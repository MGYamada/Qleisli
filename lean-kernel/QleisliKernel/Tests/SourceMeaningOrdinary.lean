import QleisliKernel.Qirf.SourceMeaningOrdinary

/-! Small complete original ordinary Meaning leaves. These controls build no
quantum program or accepted handle. Native provider/reference equality and
catalogue-duty consumption remain separate integration obligations.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceMeaningOrdinary
open QleisliKernel Finite SourceTypes Qirf
open Semantics.Exact

private abbrev Snapshot := List Nat × List Scalar × List Nat

private def inspect (sources : Sources) (name : String) : WorkM Snapshot := do
  let catalogue ← GenericCatalogue.read sources
  let meaning ← SourceMeaning.read sources (some "main") "main" name
  let [node] := meaning.graph.nodes | throw .request
  match node.action with
  | .permutation reference =>
    let checked ← Qirf.SourceMeaningOrdinary.read catalogue reference .permutation node.input.basis
    return (checked.rows.targets,checked.action.entries,checked.inputs.fields.map (·.ordinal))
  | .phase reference =>
    let checked ← Qirf.SourceMeaningOrdinary.read catalogue reference .phase node.input.basis
    return (checked.rows.targets,checked.action.entries,checked.inputs.fields.map (·.ordinal))
  | _ => throw .request

private def view (text name : String) : Option Snapshot :=
  ((inspect #[("main",text)] name).run 10000000).1.toOption

private def flip : String :=
  "#![no_implicit_prelude]\nclassical fn flip(b:Bit)->Bit{not b}meaning Flip:Bit=permutation_by(flip);"

#guard view flip "Flip" = some ([1,0],[Scalar.zero,Scalar.one,Scalar.one,Scalar.zero],[0])

private def pair : String :=
  "#![no_implicit_prelude]\nclassical fn flip_first(p:(Bit,Bit))->(Bit,Bit){let(a,b)=p;(not a,b)}" ++
  "meaning Flip:(Bit,Bit)=permutation_by(flip_first);"

-- Every original input label is present, with the first field on low axes.
#guard (view pair "Flip").map (fun (targets,_,keys) => (targets,keys)) = some ([1,0,3,2],[0,1])

private def record : String :=
  "#![no_implicit_prelude]\nstruct Packet{bit:Bit,zero:Unit}" ++
  "classical fn keep(p:Packet)->Packet{p}meaning Keep:Packet=permutation_by(keep);"

-- The complete nominal record remains one original ordinary input key.
#guard view record "Keep" = some ([0,1],[Scalar.one,Scalar.zero,Scalar.zero,Scalar.one],[0])

private def sign : String :=
  "#![no_implicit_prelude]\nclassical fn sign_bits(b:Bit)->(Bit,(Bit,Bit)){(0,(0,b))}" ++
  "meaning Sign:Bit=phase_by(sign_bits);"

#guard view sign "Sign" = some ([0,4],[Scalar.one,Scalar.zero,Scalar.zero,Semantics.PrimitiveOperator.phase 4],[0])

private def scalar : String :=
  "#![no_implicit_prelude]\nstruct Empty{}" ++
  "classical fn quarter(x:Empty)->(Bit,(Bit,Bit)){(1,(0,0))}" ++
  "meaning Quarter:Empty=phase_by(quarter);"

-- A zero-width nominal input still has its source key and scalar phase.
#guard view scalar "Quarter" = some ([1],[Semantics.PrimitiveOperator.phase 1],[0])

private def constant : String :=
  "#![no_implicit_prelude]\nclassical fn constant(b:Bit)->Bit{0}meaning Bad:Bit=permutation_by(constant);"

-- This refusal comes after the complete actual rows reveal a non-permutation.
#guard match ((inspect #[("main",constant)] "Bad").run 10000000).1 with
  | .error .notIsometric => true
  | _ => false

private def helper : String := "#![no_implicit_prelude]\npub classical fn flip(b:Bit)->Bit{not b}"
private def caller : String :=
  "#![no_implicit_prelude]\nuse helper::flip;" ++
  "classical fn through(b:Bit)->Bit{flip(b)}meaning Flip:Bit=permutation_by(through);"

#guard ((inspect #[("main",caller),("helper",helper)] "Flip").run 10000000).1.toOption =
  some ([1,0],[Scalar.zero,Scalar.one,Scalar.one,Scalar.zero],[0])

private def helperRows : Option Bool :=
  ((do
    let sources : Sources := #[("main",caller),("helper",helper)]
    let catalogue ← GenericCatalogue.read sources
    let meaning ← SourceMeaning.read sources (some "main") "main" "Flip"
    let [node] := meaning.graph.nodes | throw .request
    let .permutation reference := node.action | throw .request
    let checked ← Qirf.SourceMeaningOrdinary.read catalogue reference .permutation node.input.basis
    return checked.original.sourceRows.contains ("helper",helper) : WorkM Bool).run 10000000).1.toOption

#guard helperRows = some true

-- Existing original type/effect gates also apply to the fresh body reader;
-- these do not claim a later native equation or history refusal.
#guard (view "#![no_implicit_prelude]\nclassical fn wrong(b:Bits<1>)->Bits<1>{b}meaning Bad:Bit=permutation_by(wrong);"
  "Bad").isNone
#guard (view "#![no_implicit_prelude]\nclassical fn wrong(b:Bit)->(Bit,Bit,Bit){(b,0,0)}meaning Bad:Bit=phase_by(wrong);"
  "Bad").isNone
#guard (view "#![no_implicit_prelude]\nclassical fn wrong(b:Bit)->Bit{let q=unit();finish(q);b}meaning Bad:Bit=permutation_by(wrong);"
  "Bad").isNone
#guard (view "#![no_implicit_prelude]\nclassical fn wrong(b:Bit)->Bit{let q=unit();discard(q);b}meaning Bad:Bit=permutation_by(wrong);"
  "Bad").isNone

private def broad : String := "#![no_implicit_prelude]\npub observe fn broad(b:Bit)->Bit{b}"
private def outside : String :=
  "#![no_implicit_prelude]\nuse helper::broad;classical fn through(b:Bit)->Bit{broad(b)}" ++
  "meaning Bad:Bit=permutation_by(through);"

#guard ((inspect #[("main",outside),("helper",broad)] "Bad").run 10000000).1.isOk = false

end QleisliKernel.Tests.SourceMeaningOrdinary
