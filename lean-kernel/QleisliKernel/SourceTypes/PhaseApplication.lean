import QleisliKernel.SourceTypes.CallSyntax
import QleisliKernel.SourceTypes.CallName
import QleisliKernel.SourceTypes.StaticBindings
import QleisliKernel.SourceTypes.LexicalNatural
import QleisliKernel.SourceTypes.PhaseCoefficient

/-! Original phase parameters in the actual lexical static environment.
These witnesses supply no quantum action, effect label or execution handle;
the enclosing common traversal must check the operand and literal Raw interval.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.PhaseApplication
open QleisliKernel QleisliKernel.SourceTypes QleisliKernel.Finite

abbrev Witness {α : Type} (action : WorkM α) :=
  {value : α // ∃ work left,action.run work = (.ok value,left)}

structure Naturals (sources : Sources) where
  helpers : Witness (NaturalHelpers.prepare sources)
  environment : LexicalNatural.Environment helpers.val

def prepare (sources : Sources) : WorkM (Naturals sources) := do
  let helpers ← NaturalAffine.witness (NaturalHelpers.prepare sources)
  return ⟨helpers,LexicalNatural.empty helpers.val⟩

structure Syntax {tokens : List LocatedToken} (call : CallSyntax.Checked tokens) where
  staticCall : CallSyntax.StaticChecked call.call.callee
  numerator : CallSyntax.Argument
  denominator : CallSyntax.Argument
  staticArguments : staticCall.call.arguments = [numerator,denominator]

def readSyntax {tokens : List LocatedToken} (call : CallSyntax.Checked tokens) : Except String (Syntax call) := do
  let staticCall ← CallSyntax.readStatic call.call.callee
  match staticArguments : staticCall.call.arguments with
  | [numerator,denominator] => return ⟨staticCall,numerator,denominator,staticArguments⟩
  | _ => throw "phase requires two original static arguments"

def selected {sources caller scope tokens}
    (candidate : CallName.Checked sources caller scope tokens) : Bool :=
  match candidate.decision with
  | .primitive _ _ _ _ _ _ .phase _ => true
  | _ => false

structure Checked (sources : Sources) (caller : String) (naturals : Naturals sources)
    (scope : List String) {tokens : List LocatedToken} (call : CallSyntax.Checked tokens) where
  parsed : Syntax call
  candidate : CallName.Checked sources caller scope parsed.staticCall.call.callee
  primitive : selected candidate = true
  numerator : StaticBindings.Natural parsed.numerator.tokens
  denominator : StaticBindings.Natural parsed.denominator.tokens
  j : LexicalNatural.Checked sources caller naturals.helpers.val naturals.environment scope numerator.expression
  k : LexicalNatural.Checked sources caller naturals.helpers.val naturals.environment scope denominator.expression
  coefficient : PhaseCoefficient.Checked j.result.value k.result.value

def read (sources : Sources) (caller : String) (naturals : Naturals sources) (scope : List String)
    {tokens : List LocatedToken} (call : CallSyntax.Checked tokens) :
    WorkM (Checked sources caller naturals scope call) := do
  exactWork (Exact.charge (128*((tokens.map fun token => token.text.utf8ByteSize+4).sum+1)))
  let parsed ← lift ((readSyntax call).mapError fun _ => .request)
  let candidate ← CallName.read sources caller scope parsed.staticCall.call.callee
  if primitive : selected candidate = true then
    let numerator ← lift ((StaticBindings.natural parsed.numerator.tokens).mapError fun _ => .request)
    let denominator ← lift ((StaticBindings.natural parsed.denominator.tokens).mapError fun _ => .request)
    let j ← LexicalNatural.read sources caller naturals.helpers.val naturals.environment scope numerator.expression
    let k ← LexicalNatural.read sources caller naturals.helpers.val naturals.environment scope denominator.expression
    let coefficient ← PhaseCoefficient.read j.result.value k.result.value
    return ⟨parsed,candidate,primitive,numerator,denominator,j,k,coefficient⟩
  else throw .request

/-- Validate every original initializer, including unused ones, before making
its name visible. Completed runtime binders remain in the supplied lexical scope. -/
def extend (sources : Sources) (caller : String) {tokens : List LocatedToken}
    (leading : StaticBindings.Prefix tokens) (initial : Naturals sources) (scope : List String) :
    WorkM (Naturals sources × List String) :=
  leading.bindings.foldlM (fun (naturals,scope) binding => do
    let bound ← LexicalNatural.bind sources caller naturals.helpers.val naturals.environment
      scope binding.name.text binding.natural.expression
    let next : Naturals sources := ⟨naturals.helpers,bound.environment⟩
    return (next,binding.name.text :: scope)) (initial,scope)

end QleisliKernel.SourceTypes.PhaseApplication
