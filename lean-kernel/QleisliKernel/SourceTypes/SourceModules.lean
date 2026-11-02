import QleisliKernel.SourceTypes.SourceLookup
import QleisliKernel.SourceTypes.ModuleHeader

/-! Shared original module scans for one exact source table. A prepared table
retains declaration/lexer/policy equations and its actual preparation run.
It supplies neither a resolved name nor blanket source-row relevance, and
does not validate bodies, effects, static actuals or operation evidence.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceModules
open QleisliKernel Finite

structure Module (sources : Sources) (owner : String) where
  source : String
  items : List Declaration
  originalModule : sources.toList.filter (fun row => row.1 == owner) = [(owner,source)]
  originalItems : declarations source = .ok items
  tokens : List LocatedToken
  lexed : lexLocated source = .ok tokens
  disabled : Bool
  policy : ModuleHeader.policyTokens (tokens.map (·.text)) = .ok disabled

structure Packed (sources : Sources) where
  owner : String
  original : Module sources owner

def Packed.at {sources} (moduleData : Packed sources) (owner : String)
    (same : moduleData.owner = owner) : Module sources owner := same ▸ moduleData.original

structure Ready (sources : Sources) (modules : List (Packed sources)) : Type where
  complete : modules.map (·.owner) = sources.toList.map (·.1)
  unique : (modules.map (·.owner)).eraseDups.length = modules.length
  count : sources.size ≤ 128
  bytes : (sources.toList.map fun row => row.1.utf8ByteSize+row.2.utf8ByteSize).sum ≤ 1048576

/-- Only this table's key/coverage checks are shared. Every supplied snapshot
already binds its complete scan and exact policy to its original source row. -/
def check (sources : Sources) (modules : List (Packed sources)) : WorkM (Ready sources modules) := do
  exactWork (Exact.charge (16*((sources.toList.map fun row => row.1.utf8ByteSize+1).sum+
    (modules.map fun row => row.owner.utf8ByteSize+1).sum+1)))
  if count : sources.size ≤ 128 then
    if bytes : (sources.toList.map fun row => row.1.utf8ByteSize+row.2.utf8ByteSize).sum ≤ 1048576 then
      if complete : modules.map (·.owner) = sources.toList.map (·.1) then
        if unique : (modules.map (·.owner)).eraseDups.length = modules.length then
          pure ⟨complete,unique,count,bytes⟩
        else throw .request
      else throw .request
    else throw .limit
  else throw .limit

structure Prepared (sources : Sources) : Type where
  modules : List (Packed sources)
  ready : Ready sources modules
  invocation : ∃ before after,(check sources modules).run before = (.ok ready,after)

def prepare (sources : Sources) (modules : List (Packed sources)) : WorkM (Prepared sources) := fun before =>
  match invoked : (check sources modules).run before with
  | (.error error,after) => (.error error,after)
  | (.ok ready,after) => (.ok ⟨modules,ready,⟨before,after,invoked⟩⟩,after)

/-- Match the requested full module name in the same prepared table. Missing
modules reject; a cache miss cannot impersonate an absent declaration. -/
def lookup {sources} (prepared : Prepared sources) (owner : String) : WorkM (Module sources owner) := do
  exactWork (Exact.charge (4*((prepared.modules.map fun row => row.owner.utf8ByteSize+1).sum+
    owner.utf8ByteSize+1)))
  let some row := prepared.modules.find? (·.owner == owner) | throw .request
  if same : row.owner = owner then pure (row.at owner same) else throw .request

end QleisliKernel.SourceTypes.SourceModules
