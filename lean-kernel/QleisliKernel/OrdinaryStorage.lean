import QleisliKernel.FiniteCarrier
import QleisliKernel.Semantics.OrdinaryValue

/-! First ordinary-storage component. It interprets actual classical bindings
against an exact nominal prefix tree. Original source/type authorization, Raw
history generation, complete input domains and native transport are separate
required callers. No source runtime or accepted handle is enabled here.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.OrdinaryStorage
open Semantics.FiniteCarrier Semantics.OrdinaryValue Finite

structure BitsRead (values : Valuation) (ids : List Nat) where
  bits : List Bool
  represented : Reads values ids bits

private def bitReaders (values : Valuation) :
    Nat → ((ids : List Nat) → WorkM (BitsRead values ids)) :=
  Nat.rec (fun _ => throw .limit) (fun _ next ids => do
    match ids with
    | [] => pure ⟨[],.nil⟩
    | id :: ids =>
      exactWork (Exact.charge (values.length + 1))
      match found : lookup values id with
      | none => throw .request
      | some bit =>
        let result ← next ids
        return ⟨bit :: result.bits,.cons id bit ids result.bits found result.represented⟩)

private def readBits (values : Valuation) (ids : List Nat) : WorkM (BitsRead values ids) :=
  bitReaders values (ids.length+1) ids

structure PrefixRead (values : Valuation) (input : Basis) (storage : Storage) where
  basis : Basis
  rest : Basis
  value : Value
  partition : basis ++ rest = input
  represented : Represents values basis value storage

structure PrefixMany (values : Valuation) (input : Basis) (stores : List Storage) where
  bases : List Basis
  rest : Basis
  items : List Value
  partition : bases.flatten ++ rest = input
  represented : RepresentsMany values bases items stores

private theorem represented_lengths {values bases items stores}
    (represented : RepresentsMany values bases items stores) : bases.length = stores.length := by
  cases represented with
  | nil => rfl
  | cons basis item storage bases items stores head tail =>
    simpa using congrArg Nat.succ (represented_lengths tail)

private theorem zip_fields (fields : List (String × Storage)) :
    (fields.map Prod.fst).zip (fields.map Prod.snd) = fields := by
  induction fields with
  | nil => rfl
  | cons field fields ih => simp only [List.map_cons,List.zip_cons_cons,ih]

private structure Readers (values : Valuation) where
  one : (input : Basis) → (storage : Storage) → WorkM (PrefixRead values input storage)
  many : (input : Basis) → (stores : List Storage) → WorkM (PrefixMany values input stores)

private def readers (values : Valuation) : Nat → Readers values :=
  Nat.rec ⟨fun _ _ => throw .limit,fun _ _ => throw .limit⟩ (fun _ next => ⟨
    fun input storage => do
      exactWork (Exact.charge (input.length + values.length + 1))
      match input,storage with
      | .unit :: rest,.unit => return ⟨[.unit],rest,.unit,rfl,.unit⟩
      | .bit :: rest,.bit id =>
        match found : lookup values id with
        | none => throw .request
        | some bit => return ⟨[.bit],rest,.bit bit,rfl,.bit id bit found⟩
      | .bits width :: rest,.bits ids =>
        guard (ids.length ≤ 6) .limit
        if sized : width = ids.length then
          let result ← readBits values ids
          return ⟨[.bits ids.length],rest,.bits result.bits,by simp [sized],
            .bits ids result.bits result.represented⟩
        else throw .request
      | .enumeration origin variants :: rest,.enumeration actual ids =>
        guard (ids.length ≤ 6) .limit
        exactWork (Exact.charge (FiniteCarrier.originBytes origin + FiniteCarrier.originBytes actual + 1))
        if same : actual = origin then
          if sized : ids.length = tagBits variants.length then
            let result ← readBits values ids
            let ordinal := littleEndian result.bits
            if valid : ordinal < variants.length then
              return ⟨[.enumeration origin variants],rest,.enumeration origin ordinal,rfl,by
                subst actual
                exact .enumeration origin variants ordinal ids result.bits valid sized result.represented rfl⟩
            else throw .request
          else throw .request
        else throw .request
      | .pair :: rest,.pair first second =>
        let left ← next.one rest first
        let right ← next.one left.rest second
        return ⟨.pair :: (left.basis ++ right.basis),right.rest,.pair left.value right.value,by
          simp only [List.cons_append,List.append_assoc,right.partition,left.partition],
          .pair left.basis right.basis left.value right.value first second left.represented right.represented⟩
      | .tuple arity :: rest,.tuple stores =>
        guard (stores.length ≤ 128) .limit
        let result ← next.many rest stores
        if count : arity = result.bases.length then
          return ⟨.tuple result.bases.length :: result.bases.flatten,result.rest,.tuple result.items,by
            simp only [List.cons_append,result.partition,count],
            .tuple result.bases result.items stores result.represented⟩
        else throw .request
      | .record origin names :: rest,.record actual fields =>
        guard (fields.length ≤ 128) .limit
        exactWork (Exact.charge (FiniteCarrier.originBytes origin + FiniteCarrier.originBytes actual +
          (fields.map fun field => field.1.utf8ByteSize).sum + (names.map String.utf8ByteSize).sum + 1))
        if same : actual = origin then
          if named : fields.map Prod.fst = names then
            let result ← next.many rest (fields.map Prod.snd)
            have arity : names.length = result.bases.length := by
              have sized := represented_lengths result.represented
              have namesLength : fields.length = names.length := by
                simpa only [List.length_map] using congrArg List.length named
              exact namesLength.symm.trans (by simpa only [List.length_map] using sized.symm)
            return ⟨.record origin names :: result.bases.flatten,result.rest,
              .record origin (names.zip result.items),by simp only [List.cons_append,result.partition],by
                subst actual
                have interpreted := Represents.record origin names result.bases result.items
                  (fields.map Prod.snd) arity result.represented
                rw [← named,zip_fields] at interpreted
                simpa only [named] using interpreted⟩
          else throw .request
        else throw .request
      | _,_ => throw .request,
    fun input stores => do
      exactWork (Exact.charge (input.length + 1))
      match stores with
      | [] => return ⟨[],input,[],rfl,.nil⟩
      | first :: rest =>
        let head ← next.one input first
        let tail ← next.many head.rest rest
        return ⟨head.basis :: tail.bases,tail.rest,head.value :: tail.items,by
          simp only [List.flatten_cons,List.append_assoc,tail.partition,head.partition],
          .cons head.basis head.value first tail.bases tail.items rest head.represented tail.represented⟩⟩)

structure Checked (values : Valuation) (basis : Basis) (storage : Storage) where
  value : Value
  represented : Represents values basis value storage

/-- Freshly read actual bindings. Success gives the independent Represents
relation, including nominal identity, full shape and valid enum ordinals.
The caller still must bind original types, actual complete Raw histories and
the exact retained execution view before this can authorize any runtime. -/
def read (values : Valuation) (basis : Basis) (storage : Storage) :
    WorkM (Checked values basis storage) := do
  let _ ← FiniteCarrier.read basis
  let result ← (readers values (2*basis.length+1)).one basis storage
  if complete : result.rest = [] then
    have same : result.basis = basis := by simpa [complete] using result.partition
    return ⟨result.value,by simpa only [same] using result.represented⟩
  else throw .request

theorem Checked.represents {values basis storage} (checked : Checked values basis storage) :
    Represents values basis checked.value storage := checked.represented

theorem Checked.typed {values basis storage} (checked : Checked values basis storage) :
    ValueOf basis checked.value := checked.represented.typed

end QleisliKernel.OrdinaryStorage
