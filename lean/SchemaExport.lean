import Qleisli.Schema
import Lean

/-! Build-time export of the closed component registry, never artifact input.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
The expression tree retains every binder, universe and implicit argument.
This audit tool is outside the executable acceptance library. -/

open Lean

private def levelJson : Level → Json
  | .zero => Json.arr #[toJson "zero"]
  | .succ l => Json.arr #[toJson "succ", levelJson l]
  | .max a b => Json.arr #[toJson "max", levelJson a, levelJson b]
  | .imax a b => Json.arr #[toJson "imax", levelJson a, levelJson b]
  | .param n => Json.arr #[toJson "param", toJson n.toString]
  | .mvar n => Json.arr #[toJson "mvar", toJson n.name.toString]

private def binderJson (b : BinderInfo) : Json := toJson <| match b with
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strict_implicit"
  | .instImplicit => "instance"

private def exprJson : Expr → Json
  | .bvar i => Json.arr #[toJson "bound", toJson i]
  | .fvar i => Json.arr #[toJson "free", toJson i.name.toString]
  | .mvar i => Json.arr #[toJson "meta", toJson i.name.toString]
  | .sort l => Json.arr #[toJson "sort", levelJson l]
  | .const n ls => Json.arr #[toJson "constant", toJson n.toString, toJson (ls.map levelJson)]
  | .app f a => Json.arr #[toJson "apply", exprJson f, exprJson a]
  | .lam n t b bi => Json.arr #[toJson "lambda", toJson n.toString, binderJson bi, exprJson t, exprJson b]
  | .forallE n t b bi => Json.arr #[toJson "forall", toJson n.toString, binderJson bi, exprJson t, exprJson b]
  | .letE n t v b nondep => Json.arr #[toJson "let", toJson n.toString,
      exprJson t, exprJson v, exprJson b, toJson nondep]
  | .lit (.natVal n) => Json.arr #[toJson "nat", toJson n]
  | .lit (.strVal s) => Json.arr #[toJson "string", toJson s]
  | .mdata _ b => exprJson b
  | .proj n i b => Json.arr #[toJson "projection", toJson n.toString, toJson i, exprJson b]

private def exportDeclaration (name : Name) (theoremOnly : Bool) : Elab.Command.CommandElabM Json := do
  let env ← getEnv
  let some info := env.find? name | throwError "Missing registry declaration {name}"
  if theoremOnly then
    unless info matches .thmInfo _ do throwError "Registry soundness entry is not a theorem: {name}"
  else
    unless info matches .defnInfo _ do throwError "Registry checker is not a definition: {name}"
  if info.type.hasFVar || info.type.hasMVar || info.type.hasLooseBVars then
    throwError "Registry declaration has an open type: {name}"
  let some moduleIndex := env.getModuleIdxFor? name | throwError "Missing module for {name}"
  let readable ← Elab.Command.liftTermElabM do
    return (← Meta.ppExpr info.type).pretty
  return Json.mkObj [
    ("declaration", toJson name.toString),
    ("module", toJson env.header.moduleNames[moduleIndex.toNat]!.toString),
    ("universe_parameters", toJson (info.levelParams.map Name.toString)),
    ("type", exprJson info.type), ("readable_type", toJson readable)]

set_option format.width 100
set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true

run_cmd do
  let checker ← exportDeclaration ``QleisliKernel.Schema.check false
  let mut entries : Array Json := #[]
  for (id, name) in [
      ("qft-dyadic8/1", ``Qleisli.Schema.qft_sound),
      ("controlled-power/1", ``Qleisli.Schema.power_coherent_sound),
      ("qpe-instrument/1", ``Qleisli.Schema.qpe_sound)] do
    entries := entries.push (Json.mkObj [
      ("id", toJson id), ("theorem", ← exportDeclaration name true)])
  IO.println <| (Json.mkObj [
    ("format", toJson "qleisli.schema-type-export"), ("version", toJson (1 : Nat)),
    ("checker", checker), ("entries", Json.arr entries)]).compress
