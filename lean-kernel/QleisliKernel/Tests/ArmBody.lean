import QleisliKernel.Qirf.SourceArmBody
import QleisliKernel.Tests.ContextSectorData

/-! Two-qubit original-body controls using the frozen phase-substitution source.
The body continuation is not native admission or a general source proof.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.ArmBody
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Semantics
open Semantics.Raw Semantics.FiniteCarrier Semantics.CarrierInterface
open ContextSector

def text : String := "#![no_implicit_prelude]\npub enum Tag { A, B }\nunitary fn keep(q: Q<Bit>) -> Q<Bit> { q }\nunitary fn sign(q: Q<Bit>) -> Q<Bit> { phase[1,1](q) }\npub unitary fn route(s: Q<Tag>, q: Q<Bit>) -> (Q<Tag>, Q<Bit>) {\n    qmatch(s, q) { Tag::B => sign, Tag::A => keep }\n}\nfn main() -> Unit { () }\n"

def tag (source : String := text) : Basis := [.enumeration ⟨"main","Tag",source⟩ ["A","B"]]
def offset (source : String := text) : Nat := (SourceTypes.QuantumSequence.originalOffsets
  ((SourceTypes.lexLocated source).toOption.getD []))[0]?.getD 0

def main (exponent : Nat) : Observation.Program :=
  ⟨[⟨0,[0],1⟩,⟨1,[1],1⟩],[],
    [.pure (.join 0 1 2),
     .pure (.applyUnitary 2 3 [Tests.ContextSectorTests.phaseStep exponent]),
     .pure (.split 3 4 5 1)], [4,5],[],.unitary⟩
def identityBody : Observation.Program := ⟨[⟨10,[7],1⟩],[],[],[10],[],.unitary⟩
def artifact (exponent : Nat) (source : String := text) : Qirf.Artifact :=
  ⟨#[main exponent,identityBody,Tests.ContextSectorTests.controlled 0,
      Tests.ContextSectorTests.arm exponent,Tests.ContextSectorTests.controlled exponent],
    #[⟨[.bit],1,.phase8 [0,0],"main::keep","independent::identity",[0]⟩,
      ⟨[.bit],3,.phase8 [0,exponent],"main::sign","independent::phase",[0]⟩],
    #[("main",source)],0,none⟩
def order : Array Nat := #[1,2,3,4,5,6,0]
def interface (source : String := text) : Interface :=
  ⟨[⟨⟨0,[0],1⟩,tag source⟩,⟨⟨1,[1],1⟩,[.bit]⟩],
   [⟨⟨4,[0],1⟩,tag source⟩,⟨⟨5,[1],1⟩,[.bit]⟩],.unitary⟩
def requests (source : String := text) : List Request := [⟨interface source,interface source,⟨offset source,0,3⟩,[⟨1,4⟩,⟨0,2⟩]⟩]
def positions (source : String := text) : List Position := [⟨offset source,0,3⟩]

def bodyChecked (exponent index : Nat) (missing : Bool := false) (delta : Nat := 0)
    (source : String := text) : Finite.WorkM Nat := do
  let checked ← ContextSector.check (artifact exponent source) order "main" "route" (positions source) (requests source)
  let some site := checked.locals.head? | throw .request
  let some arm := site.checked.prepared.entries.val[index]? | throw .request
  let tokens := arm.bound.signature.original.occurrence.body
  let phaseOffset := ((tokens.find? (·.text == "phase")).map (·.span.startByte)).getD 0
  let placed := if index == 0 && !missing then [⟨phaseOffset+delta,0,1⟩] else []
  let body ← SourceArmBody.check checked.body.root arm.bound arm.checked placed
  return body.body.val.whole.operations.length

#guard ((bodyChecked 4 0).run 10000000).1.toOption == some 1
#guard ((bodyChecked 4 1).run 10000000).1.toOption == some 0
-- Source/names remain unchanged; the main, arm, specification and control all
-- agree on the wrong identity. The original phase body must still reject it.
#guard ((bodyChecked 0 0).run 10000000).1 matches .error .equation
#guard ((bodyChecked 4 0 true).run 10000000).1 matches .error .request
#guard ((bodyChecked 4 0 false 1).run 10000000).1 matches .error .request

-- Pure IR and a matching control cannot hide original observing behavior.
-- Frozen measure counterexample: 81d7704db119491d7538342c786a1e08d5d57c9369971f5d6c5f6e6f0a2aad7b
def measureText : String := "#![no_implicit_prelude]\npub enum Tag { A, B }\nunitary fn keep(q: Q<Bit>) -> Q<Bit> { q }\nunitary fn sign(q: Q<Bit>) -> Q<Bit> { let b = measure_z(q); basis unit(()) as _ { 0 } }\npub unitary fn route(s: Q<Tag>, q: Q<Bit>) -> (Q<Tag>, Q<Bit>) {\n    qmatch(s, q) { Tag::B => sign, Tag::A => keep }\n}\nfn main() -> Unit { () }\n"
#guard ((bodyChecked 0 0 false 0 measureText).run 10000000).1 matches .error .request

-- Frozen reset counterexample: a40fbed06bef2c2506989c58060f09aa1226513ab67b8162ee7bb05426a9ba89
def resetText : String := "#![no_implicit_prelude]\npub enum Tag { A, B }\nunitary fn keep(q: Q<Bit>) -> Q<Bit> { q }\nobserve fn reset(q: Q<Bit>) -> Q<Bit> { discard(q); basis unit(()) as _ { 0 } }\nunitary fn sign(q: Q<Bit>) -> Q<Bit> { reset(q) }\npub unitary fn route(s: Q<Tag>, q: Q<Bit>) -> (Q<Tag>, Q<Bit>) {\n    qmatch(s, q) { Tag::B => sign, Tag::A => keep }\n}\nfn main() -> Unit { () }\n"
#guard ((bodyChecked 0 0 false 0 resetText).run 10000000).1 matches .error .request

-- Frozen discard counterexample: 945a0e969d2665e21b1ce10a9b3efb48b4251148fdce5e3502a630abb8f98d63
def discardText : String := "#![no_implicit_prelude]\npub enum Tag { A, B }\nunitary fn keep(q: Q<Bit>) -> Q<Bit> { q }\nunitary fn sign(q: Q<Bit>) -> Q<Bit> { discard(q); basis unit(()) as _ { 0 } }\npub unitary fn route(s: Q<Tag>, q: Q<Bit>) -> (Q<Tag>, Q<Bit>) {\n    qmatch(s, q) { Tag::B => sign, Tag::A => keep }\n}\nfn main() -> Unit { () }\n"
#guard ((bodyChecked 0 0 false 0 discardText).run 10000000).1 matches .error .request

end QleisliKernel.Tests.ArmBody
