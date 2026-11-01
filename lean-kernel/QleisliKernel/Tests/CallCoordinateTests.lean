import QleisliKernel.Tests.CallSyntaxTests
import QleisliKernel.Tests.RawTraceTests
import QleisliKernel.Tests.ContextSectorTests

/-! Internal context-profile coordinates, using at most two bits.
The preserved opening-parenthesis prototype is a distinct earlier profile;
these tests do not assert compatibility or semantic equivalence between them.
No native handle or complete source-preservation claim is supplied.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.CallCoordinateTests
open QleisliKernel.Qirf
open QleisliKernel.SourceTypes
open QleisliKernel QleisliKernel.Semantics QleisliKernel.Tests.RawTraceTests

def callCoordinates (text : String) : Option (Nat × Nat) := do
  let tokens ← (SourceTypes.lexLocated text).toOption
  let checked ← (CallSyntax.read tokens).toOption
  return (checked.calleeOffset,checked.call.opening.span.startByte)

def observed (text : String) : Option (List Nat × List Nat) :=
  ((SourceTrace.read (sources text) "main" "route").run 10000000).1.toOption.map
    fun checked => (checked.callOffsets,checked.result.events.map QleisliKernel.Qirf.RawTrace.offset)

/-- Retain the actual previous coordinate from original tokens, including
long callee names and comments; do not approximate it by adding one byte. -/
def oldOffsets (text : String) : Option (List Nat) :=
  ((SourceTrace.read (sources text) "main" "route").run 10000000).1.toOption.map
    fun checked => checked.result.events.map fun event => match event with
      | .primitive event => event.call.call.opening.span.startByte
      | .phase event => event.call.call.opening.span.startByte
      | .selection event .. => event.parsed.keyword.span.startByte

def checksOffsets (text : String) (program : Observation.Program) (counts offsets : List Nat) : Bool :=
  checks text program counts (fun positions => (positions.zip offsets).map
    fun (position,offset) => {position with offset}) 10000000

def oldRefuses (text : String) (program : Observation.Program) (counts : List Nat) : Bool :=
  match oldOffsets text with
  | none => false
  | some offsets => !checksOffsets text program counts offsets

def oldContextPositions : List QleisliKernel.Qirf.RawTrace.Position :=
  match oldOffsets ContextSectorTests.text with
  | none => []
  | some offsets => (ContextSectorTests.positions.zip offsets).map
      fun (position,offset) => {position with offset}

def controls : List (String × Bool) := [
  ("UTF8 before callee uses exact bytes",callCoordinates "/*λ*/h(q)" == some (6,7)),
  ("comment separates callee and opening",callCoordinates "h /*λ*/ (q)" == some (0,9)),
  ("newline separates callee and opening",callCoordinates "h\n(q)" == some (0,2)),
  ("qualified segmentation names first segment only",callCoordinates "defs::h(q)" == some (0,7)),
  ("source UTF8 callee coordinate",observed (single "/*λ*/h(q)") == some ([45],[45])),
  ("source comment callee coordinate",observed (single "h /*λ*/ (q)") == some ([39],[39])),
  ("grouping does not widen the callee span",observed (single "((h(q)))") == some ([41],[41])),
  ("nested calls retain actual inner then outer order",observed (single "h(h(q))") == some ([41,39],[41,39])),
  ("nested comments retain byte coordinates",observed (single "h /*λ*/ (h(q))") == some ([49,39],[49,39])),
  ("cached same-name calls retain distinct occurrences",
    observed (single "let q=h(q);h(q)") == some ([45,50],[45,50])),
  ("selection keeps its keyword coordinate",observed mixedSource == some ([135],[135,149])),
  ("literal callee position passes",checksOffsets (single "h(q)") oneH [1] [39]),
  ("UTF8 source position passes",checksOffsets (single "/*λ*/h(q)") oneH [1] [45]),
  ("comment source position passes",checksOffsets (single "h /*λ*/ (q)") oneH [1] [39]),
  ("grouped callee position passes",checksOffsets (single "((h(q)))") oneH [1] [41]),
  ("broad grouped expression position refuses",!checksOffsets (single "((h(q)))") oneH [1] [39]),
  ("nested actual postorder passes",checksOffsets (single "h(h(q))") twoH [1,1] [41,39]),
  ("numeric source order refuses",!checksOffsets (single "h(h(q))") twoH [1,1] [39,41]),
  ("omitted occurrence refuses",!checksOffsets (single "h(h(q))") twoH [1,1] [41]),
  ("duplicate occurrence refuses",!checksOffsets (single "h(h(q))") twoH [1,1] [41,41]),
  ("old literal opening refuses",oldRefuses (single "h(q)") oneH [1]),
  ("old UTF8 opening refuses",oldRefuses (single "/*λ*/h(q)") oneH [1]),
  ("old comment opening refuses",oldRefuses (single "h /*λ*/ (q)") oneH [1]),
  ("old nested openings refuse",oldRefuses (single "h(h(q))") twoH [1,1]),
  ("long primitive uses original callee",observed scalarSource == some ([41],[41])),
  ("long primitive old opening refuses",oldRefuses scalarSource scalarZero [1]),
  ("qualified name does not gain primitive fallback",!checks (single "std::h(q)") oneH [1]),
  ("constructed callee remains unsupported",!checks (single "power(h,2)(q)") twoH [2]),
  ("static callee remains unsupported",!checks (single "phase[1,1](q)") oneH [1]),
  ("complete context passes with callee positions",ContextSectorTests.result.toOption == some [2,2]),
  ("complete context rejects previous opening positions",
    (ContextSectorTests.failure ContextSectorTests.artifact ContextSectorTests.requests oldContextPositions).isSome)]

#guard controls.length = 31
#guard controls.all (·.2)
#print axioms CallSyntax.Checked.calleeToken_original
end QleisliKernel.Tests.CallCoordinateTests
