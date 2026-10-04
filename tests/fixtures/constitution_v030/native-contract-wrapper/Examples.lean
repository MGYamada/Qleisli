import Qleisli.NativeContract
import QleisliKernel.Qirf.Contract
/-! Three small executable wrapper examples. The generic correspondence theorem
is checked separately in Review.lean; these examples do not exercise the byte
codec, Rust transport, or prove compiled native execution correct.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.NativeContract.WrapperExamples
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite
open QleisliKernel.Finite

def unitMinus : Matrix := ⟨1,1,[QleisliKernel.Exact.Scalar.phase 4]⟩
def tGate : Matrix := ⟨2,2,[.one,.zero,.zero,QleisliKernel.Exact.Scalar.phase 1]⟩
def asymmetric : Matrix := ⟨4,4,
  [.zero,.zero,QleisliKernel.Exact.Scalar.phase 2,.zero,
   .one,.zero,.zero,.zero,
   .zero,.zero,.zero,QleisliKernel.Exact.Scalar.phase 4,
   .zero,QleisliKernel.Exact.Scalar.phase 1,.zero,.zero]⟩
def identity (n : Nat) : Matrix := ⟨n,n,(List.range (n*n)).map
  (fun index => if index / n == index % n then Scalar.one else Scalar.zero)⟩
def contract (signature : Basis) (meaning : Matrix) : Contract :=
  ⟨⟨signature,signature,identity meaning.rows⟩,
   ⟨signature,signature,identity meaning.rows⟩,meaning⟩
def reconstructs (signature : Basis) (meaning : Matrix) : Bool :=
  match (circuitMatrix [⟨signature,meaning⟩] (QleisliKernel.Qirf.contractCircuit signature)).run 1000000 with
  | (.ok actual,_) => actual == meaning
  | _ => false
def checks (signature : Basis) (meaning : Matrix) : Bool :=
  let required := contract signature meaning
  match (check [⟨signature,meaning⟩] (QleisliKernel.Qirf.contractCircuit signature) required required).run 1000000 with
  | (.ok actual,_) => actual == meaning
  | _ => false

example : reconstructs [.unit] unitMinus = true := by decide
example : reconstructs [.bit] tGate = true := by decide
example : reconstructs [.pair,.bit,.bit] asymmetric = true := by decide
example : checks [.unit] unitMinus = true := by decide
example : checks [.bit] tGate = true := by decide
-- The 4-by-4 full contract is checked operationally below. Kernel reduction
-- of that concrete arithmetic exceeds the ordinary elaboration heartbeat budget;
-- the general coefficient/encoded theorem is separately typechecked.
def rejectsLogical (signature : Basis) (meaning logical : Matrix) : Bool :=
  let required := contract signature logical
  match (check [⟨signature,meaning⟩] (QleisliKernel.Qirf.contractCircuit signature) required required).run 1000000 with
  | (.error .equation,_) => true
  | _ => false

def tInverse : Matrix := ⟨2,2,[.one,.zero,.zero,QleisliKernel.Exact.Scalar.phase 7]⟩
def transpose (matrix : Matrix) : Matrix := ⟨matrix.cols,matrix.rows,
  (List.range (matrix.rows*matrix.cols)).map (fun index => matrix.entry (index % matrix.rows) (index / matrix.rows))⟩

#eval show IO Unit from do
  for (name,result) in [
      ("unit-minus/reconstruct",reconstructs [.unit] unitMinus),
      ("t/reconstruct",reconstructs [.bit] tGate),
      ("two-bit-asymmetric/reconstruct",reconstructs [.pair,.bit,.bit] asymmetric),
      ("unit-minus/contract",checks [.unit] unitMinus),
      ("t/contract",checks [.bit] tGate),
      ("two-bit-asymmetric/contract",checks [.pair,.bit,.bit] asymmetric),
      ("unit-minus/reject-plus-one",rejectsLogical [.unit] unitMinus (identity 1)),
      ("t/reject-inverse",rejectsLogical [.bit] tGate tInverse),
      ("two-bit-asymmetric/reject-transpose",rejectsLogical [.pair,.bit,.bit] asymmetric (transpose asymmetric))] do
    unless result do throw (IO.userError s!"FAIL: {name}")
    IO.println s!"PASS: {name}"

end Qleisli.NativeContract.WrapperExamples
