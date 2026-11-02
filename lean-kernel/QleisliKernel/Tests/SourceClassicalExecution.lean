import QleisliKernel.Qirf.SourceClassicalExecution

/-! Small exact independent-interpreter execution controls. These use no
quantum program, producer summary, original-source authority or accepted handle.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceClassicalExecution
open QleisliKernel Finite Semantics.FiniteCarrier Semantics.SourceClassical

private def inspect (functions : List Function) (arguments : List Value) : WorkM Value := do
  let metadata ← Qirf.SourceClassicalExecution.readMetadata functions
  return (← Qirf.SourceClassicalExecution.read metadata (functions.length+1) 0 arguments).val

private def invert : Function :=
  ⟨[[.bit]],[.bit],[[.name "b"]],[.variable "b",.not 0],1⟩

#guard ((inspect [invert] [[.ordinary [.bit] 0]]).run 10000000).1.toOption =
  some [.ordinary [.bit] 1]
#guard ((inspect [invert] [[.ordinary [.bit] 1]]).run 10000000).1.toOption =
  some [.ordinary [.bit] 0]

-- The unselected undefined call is not evaluated. Changing only the original
-- condition selects it and genuinely refuses; metadata preparation is shared.
private def selectedOnly (condition : Bool) : Function :=
  ⟨[],[.bit],[],[.bit condition,.call 7 [],.bit false,.conditional 0 1 2],3⟩

#guard ((inspect [selectedOnly false] []).run 10000000).1.toOption =
  some [.ordinary [.bit] 0]
#guard match ((inspect [selectedOnly true] []).run 10000000).1 with
  | .error .request => true
  | _ => false

private def tag : Basis :=
  [.enumeration ⟨"main","Tag","enum Tag{A,B,C}"⟩ ["A","B","C"]]
private def foreign : Basis :=
  [.enumeration ⟨"other","Tag","enum Tag{A,B,C}"⟩ ["A","B","C"]]

private def cycle : Function :=
  ⟨[tag],tag,[[.name "tag"]],
    [.variable "tag",.variant tag 0,.variant tag 1,.variant tag 2,.matching 0 [2,0,1] [1,2,3]],4⟩

#guard ((inspect [cycle] [[.ordinary tag 0]]).run 10000000).1.toOption = some [.ordinary tag 1]
#guard ((inspect [cycle] [[.ordinary tag 2]]).run 10000000).1.toOption = some [.ordinary tag 0]
#guard match ((inspect [cycle] [[.ordinary foreign 0]]).run 10000000).1 with
  | .error .request => true
  | _ => false

-- Five occurrences share one exact immutable type receipt. The complete
-- original nominal origin remains present; no same-width substitution occurs.
#guard (((Qirf.SourceClassicalExecution.readMetadata [cycle]).map fun metadata =>
  metadata.entries.map (·.basis)).run 10000000).1.toOption = some [tag]

-- Ordinary tuples can contain several bounded scalar fields. The cache does
-- not join their codes or introduce a six-bit limit on the complete tuple.
private def tupleInput : Function :=
  ⟨[[.pair,.bits 4,.bits 4]],[.unit],[[.name "pair"]],[.unit],0⟩

#guard ((inspect [tupleInput] [[.tuple 2,.ordinary [.bits 4] 0,.ordinary [.bits 4] 0]]).run
  10000000).1.toOption = some [.ordinary [.unit] 0]

private def wrongResult : Function :=
  ⟨[[.bit]],[.unit],[[.name "b"]],[.variable "b"],0⟩

#guard match ((inspect [wrongResult] [[.ordinary [.bit] 0]]).run 10000000).1 with
  | .error .request => true
  | _ => false

#guard match ((inspect [invert] [[.ordinary [.bit] 0]]).run 0).1 with
  | .error (.arithmetic .workLimit) => true
  | _ => false

end QleisliKernel.Tests.SourceClassicalExecution
