import QleisliKernel.Semantics.SourceOrdinary

/-! Independent finite ordinary program evaluation.
Programs contain ordinary expression trees, original nominal field order and
explicit callees. This module imports no source reader, acceptance checker,
symbolic summary, Raw program or producer table. Binding these data to original
source syntax is a separate native-reader obligation. Fuel exhaustion refuses;
ordinary conditions evaluate only their selected branch.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Semantics.SourceClassical
open FiniteCarrier
abbrev Value := SourceOrdinary.Result
abbrev Environment := List (String × Value)

inductive PatternAtom where
  | name (name : String) | wildcard | tuple (arity : Nat)
  deriving BEq, DecidableEq, Repr

abbrev Pattern := List PatternAtom

private def spanBasis : Nat → Nat → Basis → Basis → Except String (Basis × Basis) :=
  Nat.rec (fun _ _ _ => throw "ordinary basis traversal capacity") (fun _ next pending tokens reversed => do
    if pending == 0 then return (reversed.reverse,tokens)
    let atom :: rest := tokens | throw "incomplete ordinary basis"
    next (pending-1+(children atom).getD 0) rest (atom :: reversed))

def splitBasis (basis : Basis) : Except String (Basis × Basis) :=
  spanBasis (basis.length+1) 1 basis []

def basisFields (basis : Basis) : Except String (List Basis) := do
  let first :: rest := basis | throw "empty ordinary tuple basis"
  let arity ← match first with
    | .pair => pure 2
    | .tuple arity => pure arity
    | _ => throw "ordinary basis is not a tuple"
  let (fields,rest) ← (List.range arity).foldlM (fun (fields,rest) _ => do
    let (field,rest) ← splitBasis rest
    return (fields ++ [field],rest)) ([],rest)
  if !rest.isEmpty then throw "trailing ordinary tuple basis"
  return fields

private def spanValue : Nat → Nat → Value → Value → Except String (Value × Value) :=
  Nat.rec (fun _ _ _ => throw "ordinary value traversal capacity") (fun _ next pending tokens reversed => do
    if pending == 0 then return (reversed.reverse,tokens)
    let atom :: rest := tokens | throw "incomplete ordinary value"
    match atom with
    | .owner _ => throw "quantum value in an ordinary program"
    | .ordinary .. => next (pending-1) rest (atom :: reversed)
    | .tuple arity => next (pending-1+arity) rest (atom :: reversed))

def splitValue (value : Value) : Except String (Value × Value) :=
  spanValue (value.length+1) 1 value []

def valueBasis (value : Value) : Except String Basis :=
  value.foldlM (fun basis atom => match atom with
    | .owner _ => throw "quantum value in an ordinary program"
    | .ordinary field ordinal => do
      let some dimension := FiniteCarrier.dimension field | throw "invalid ordinary scalar type"
      if ordinal ≥ dimension then throw "ordinary scalar outside its type"
      pure (basis ++ field)
    | .tuple arity => pure (basis ++ [if arity == 2 then .pair else .tuple arity])) []

structure Packed where
  basis : Basis
  ordinal : Nat
  dimension : Nat
  deriving BEq, DecidableEq, Repr

/-- Logical first-field-fast tuple coordinates; nominal values stay atomic. -/
def pack (value : Value) : Except String Packed := do
  let stack ← value.reverse.foldlM (fun (stack : List Packed) atom => do
    match atom with
    | .owner _ => throw "quantum value in an ordinary result"
    | .ordinary basis ordinal =>
      let some dimension := FiniteCarrier.dimension basis | throw "invalid ordinary result basis"
      if ordinal ≥ dimension then throw "ordinary result outside its basis"
      return ⟨basis,ordinal,dimension⟩ :: stack
    | .tuple arity =>
      if arity > stack.length then throw "ordinary result tuple shape"
      let fields := stack.take arity
      let (ordinal,dimension) := fields.foldl (fun (ordinal,stride) field =>
        (ordinal+stride*field.ordinal,stride*field.dimension)) (0,1)
      let basis := (if arity == 2 then Atom.pair else .tuple arity) :: fields.flatMap (·.basis)
      return ⟨basis,ordinal,dimension⟩ :: stack.drop arity) ([] : List Packed)
  let [result] := stack | throw "ordinary result multiplicity"
  return result

private def expandWith : Nat → Basis → Nat → Except String Value :=
  Nat.rec (fun _ _ => throw "ordinary expansion capacity") (fun _ next basis ordinal => do
    let some dimension := FiniteCarrier.dimension basis | throw "invalid ordinary basis"
    if ordinal ≥ dimension then throw "ordinary label outside its basis"
    match basis with
    | .pair :: _ | .tuple _ :: _ =>
      let fields ← basisFields basis
      let (values,remaining) ← fields.foldlM (fun (values,remaining) field => do
        let some dimension := FiniteCarrier.dimension field | throw "invalid ordinary field basis"
        if dimension == 0 then throw "empty ordinary field"
        let value ← next field (remaining % dimension)
        return (values ++ value,remaining / dimension)) ([],ordinal)
      if remaining != 0 then throw "trailing ordinary tuple label"
      return .tuple fields.length :: values
    | _ => return [.ordinary basis ordinal])

def expand (basis : Basis) (ordinal : Nat) : Except String Value :=
  expandWith (basis.length+1) basis ordinal

private def bindValue : Nat → Pattern → Value → Environment →
    Except String (Pattern × Value × Environment) :=
  Nat.rec (fun _ _ _ => throw "ordinary binding capacity") (fun _ next pattern value environment => do
    let first :: rest := pattern | throw "incomplete ordinary pattern"
    match first with
    | .name name =>
      let (selected,tail) ← splitValue value
      return (rest,tail,(name,selected) :: environment.filter (·.1 != name))
    | .wildcard =>
      let (_,tail) ← splitValue value
      return (rest,tail,environment)
    | .tuple 0 =>
      let .ordinary [.unit] 0 :: tail := value | throw "Unit pattern requires ordinary Unit"
      return (rest,tail,environment)
    | .tuple arity =>
      let .tuple actual :: tail := value | throw "ordinary tuple pattern requires a tuple value"
      if arity != actual then throw "ordinary tuple pattern arity"
      (List.range arity).foldlM (fun (pattern,value,environment) _ => next pattern value environment)
        (rest,tail,environment))

def bind (pattern : Pattern) (value : Value) (environment : Environment) : Except String Environment := do
  let (rest,tail,environment) ← bindValue (pattern.length+1) pattern value environment
  if !rest.isEmpty || !tail.isEmpty then throw "ordinary binding shape"
  return environment

private def bindTypesWith : Nat → Pattern → List Basis → List (String × Basis) →
    Except String (Pattern × List Basis × List (String × Basis)) :=
  Nat.rec (fun _ _ _ => throw "ordinary pattern type capacity") (fun _ next pattern values environment => do
    let first :: rest := pattern | throw "incomplete ordinary type pattern"
    let value :: tail := values | throw "missing ordinary pattern type"
    match first with
    | .name name => return (rest,tail,(name,value) :: environment.filter (·.1 != name))
    | .wildcard => return (rest,tail,environment)
    | .tuple 0 =>
      if value != [.unit] then throw "Unit pattern requires its exact ordinary type"
      return (rest,tail,environment)
    | .tuple arity =>
      let fields ← basisFields value
      if fields.length != arity then throw "ordinary pattern type arity"
      let (rest,remaining,environment) ← (List.range arity).foldlM
        (fun (pattern,values,environment) _ => next pattern values environment) (rest,fields,environment)
      if !remaining.isEmpty then throw "ordinary pattern type fields"
      return (rest,tail,environment))

def bindTypes (pattern : Pattern) (basis : Basis) (environment : List (String × Basis)) :
    Except String (List (String × Basis)) := do
  let (rest,tail,environment) ← bindTypesWith (pattern.length+1) pattern [basis] environment
  if !rest.isEmpty || !tail.isEmpty then throw "ordinary type binding shape"
  return environment

structure Record where
  basis : Basis
  fields : List (String × Basis)
  deriving BEq, DecidableEq, Repr

inductive Node where
  | unit | bit (value : Bool) | emptyBits
  | variable (name : String)
  | tuple (fields : List Nat)
  | not (child : Nat) | xor (first second : Nat) | and (first second : Nat)
  | conditional (condition thenBody elseBody : Nat)
  | staticConditional (selected : Bool) (thenBody elseBody : Nat)
  | binding (pattern : Pattern) (value rest : Nat)
  | sequence (first rest : Nat)
  | variant (basis : Basis) (ordinal : Nat)
  | record (original : Record) (written : List (String × Nat))
  | projection (original : Record) (index receiver : Nat)
  | matching (scrutinee : Nat) (labels bodies : List Nat)
  | call (function : Nat) (arguments : List Nat)
  deriving BEq, DecidableEq, Repr

def Node.children : Node → List Nat
  | .unit | .bit _ | .emptyBits | .variable _ | .variant .. => []
  | .tuple fields | .call _ fields => fields
  | .not child => [child]
  | .xor first second | .and first second | .staticConditional _ first second |
    .binding _ first second | .sequence first second => [first,second]
  | .conditional condition first second => [condition,first,second]
  | .record _ written => written.map (·.2)
  | .projection _ _ receiver => [receiver]
  | .matching scrutinee _ bodies => scrutinee :: bodies

structure Function where
  inputs : List Basis
  output : Basis
  patterns : List Pattern
  nodes : List Node
  root : Nat
  deriving BEq, DecidableEq, Repr

def bitValue (value : Value) : Except String Nat := do
  let [.ordinary [.bit] ordinal] := value | throw "ordinary Boolean type"
  if ordinal ≥ 2 then throw "ordinary Boolean label"
  return ordinal

def construct (original : Record) (written : List (String × Value)) : Except String Value := do
  if !decide (written.map (·.1)).Nodup then throw "duplicate ordinary record field"
  if !decide ((original.fields.map (·.1)).Perm (written.map (·.1))) then throw "ordinary record field coverage"
  let (ordinal,_) ← original.fields.foldlM (fun (ordinal,stride) (name,basis) => do
    let some (_,value) := written.find? (·.1 == name) | throw "missing ordinary record field"
    let field ← pack value
    if field.basis != basis then throw "ordinary record field exact type"
    return (ordinal+stride*field.ordinal,stride*field.dimension)) (0,1)
  return [.ordinary original.basis ordinal]

def project (original : Record) (index : Nat) (value : Value) : Except String Value := do
  let [.ordinary basis ordinal] := value | throw "ordinary projection receiver shape"
  if basis != original.basis then throw "ordinary projection receiver exact type"
  let some (_,field) := original.fields[index]? | throw "ordinary projection field index"
  let dimensions ← original.fields.mapM fun (_,basis) => do
    let some dimension := FiniteCarrier.dimension basis | throw "ordinary field basis"
    return dimension
  let some dimension := dimensions[index]? | throw "ordinary projection field dimension"
  let stride := (dimensions.take index).foldl (·*·) 1
  if stride == 0 || dimension == 0 then throw "empty ordinary field carrier"
  expand field ((ordinal/stride)%dimension)

def selectMatch (labels bodies : List Nat) (value : Value) : Except String Nat := do
  let [.ordinary _ ordinal] := value | throw "ordinary match scrutinee shape"
  if labels.length != bodies.length || !decide labels.Nodup then throw "ordinary match label table"
  let position := labels.idxOf ordinal
  let some selected := bodies[position]? | throw "ordinary match has no matching label"
  return selected

def nodeAction (callee : Nat → List Value → Except String Value)
    (next : Environment → Nat → Except String Value) (environment : Environment) (node : Node) :
    Except String Value := do
      let child (index : Nat) := next environment index
      match node with
      | .unit => return [.ordinary [.unit] 0]
      | .bit value => return [.ordinary [.bit] (if value then 1 else 0)]
      | .emptyBits => return [.ordinary [.bits 0] 0]
      | .variable name =>
        let some (_,value) := environment.find? (·.1 == name) | throw "unknown ordinary binding"
        return value
      | .tuple fields => return .tuple fields.length :: (← fields.mapM child).flatten
      | .not input =>
        let value ← bitValue (← child input)
        return [.ordinary [.bit] (1-value)]
      | .xor first second =>
        let a ← bitValue (← child first)
        let b ← bitValue (← child second)
        return [.ordinary [.bit] (if a == b then 0 else 1)]
      | .and first second =>
        let a ← bitValue (← child first)
        let b ← bitValue (← child second)
        return [.ordinary [.bit] (if a == 1 && b == 1 then 1 else 0)]
      | .conditional condition left right =>
        let selected ← bitValue (← child condition)
        child (if selected == 1 then left else right)
      | .staticConditional selected left right => child (if selected then left else right)
      | .binding pattern value rest =>
        let value ← child value
        let environment ← bind pattern value environment
        next environment rest
      | .sequence first rest =>
        let _ ← child first
        child rest
      | .variant basis ordinal =>
        let some dimension := FiniteCarrier.dimension basis | throw "ordinary variant basis"
        if ordinal ≥ dimension then throw "ordinary variant label"
        return [.ordinary basis ordinal]
      | .record original written =>
        let values ← written.mapM fun (name,index) => do return (name,← child index)
        construct original values
      | .projection original field receiver => project original field (← child receiver)
      | .matching scrutinee labels bodies =>
        child (← selectMatch labels bodies (← child scrutinee))
      | .call function arguments => callee function (← arguments.mapM child)

def evaluateNode (nodes : List Node) (callee : Nat → List Value → Except String Value) :
    Nat → Environment → Nat → Except String Value :=
  Nat.rec (fun _ _ => throw "ordinary expression evaluation capacity")
    (fun _ next environment index => do
      let some node := nodes[index]? | throw "missing ordinary expression node"
      nodeAction callee next environment node)

theorem evaluateNode_succ (nodes : List Node) (callee : Nat → List Value → Except String Value)
    (fuel : Nat) (environment : Environment) (index : Nat) :
    evaluateNode nodes callee (fuel+1) environment index = (do
      let some node := nodes[index]? | throw "missing ordinary expression node"
      nodeAction callee (evaluateNode nodes callee fuel) environment node) := rfl

/-- Functions refer to explicit original callees. The adapter supplies their
acyclic source order; neither an undefined callee nor exhausted fuel has a
default result. Complete declared argument/result trees remain distinct. -/
def bindArguments (function : Function) (arguments : List Value) : Except String Environment := do
    if arguments.length != function.patterns.length || arguments.length != function.inputs.length then
      throw "ordinary call arity"
    let types ← arguments.mapM valueBasis
    if types != function.inputs then throw "ordinary call exact input types"
    (function.patterns.zip arguments).foldlM
      (fun environment (pattern,value) => bind pattern value environment) []

def checkResult (output : Basis) (result : Value) : Except String Value := do
    if (← valueBasis result) != output then throw "ordinary call exact result type"
    return result

def functionAction (next : Nat → List Value → Except String Value)
    (function : Function) (arguments : List Value) : Except String Value := do
    let environment ← bindArguments function arguments
    let result ← evaluateNode function.nodes next (function.nodes.length+1) environment function.root
    checkResult function.output result

def evaluate (functions : List Function) : Nat → Nat → List Value → Except String Value :=
  Nat.rec (fun _ _ => throw "ordinary call evaluation capacity") (fun _ next index arguments => do
    let some function := functions[index]? | throw "missing ordinary callee"
    functionAction next function arguments)

theorem evaluate_succ (functions : List Function) (fuel index : Nat) (arguments : List Value) :
    evaluate functions (fuel+1) index arguments = (do
      let some function := functions[index]? | throw "missing ordinary callee"
      functionAction (evaluate functions fuel) function arguments) := rfl

end QleisliKernel.Semantics.SourceClassical
