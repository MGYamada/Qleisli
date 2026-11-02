import QleisliKernel.Qirf.RuntimeInterval

/-! Complete logical-role/physical-port boundaries for mixed source bodies.
The enclosing original-source traversal derives the roles and transition maps.
These checks bind them to every actual live port, with no width-based owner
identification and no omission of separate zero-width owners. They alone grant
neither source preservation, code-space equations nor execution authority.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeOwnerMap
open QleisliKernel QleisliKernel.Finite
abbrev Owner := Semantics.SourceOwners.Owner
abbrev Port := Semantics.Raw.Port
abbrev State := Raw.Observation.State

structure Binding where
  owner : Owner
  port : Port
  deriving DecidableEq

abbrev Map := List Binding

def byOwner (bindings : Map) (owner : Owner) : Option Binding :=
  bindings.find? (fun binding => binding.owner == owner)

def byToken (bindings : Map) (token : Nat) : Option Binding :=
  bindings.find? (fun binding => binding.port.token == token)

structure Checked (roles : List Owner) (state : State) where
  bindings : Map
  ordered : bindings.map (·.owner) = roles
  ownersDistinct : (roles.map (·.ordinal)).Nodup
  tokensDistinct : (bindings.map (·.port.token)).Nodup
  complete : (bindings.map (·.port)).Perm state.quantum.live

/-- The full live frame must occur exactly once. Exact ordered source roles
are an input from the original body continuation, never transport flags. -/
def check (roles : List Owner) (state : State) (bindings : Map) : WorkM (Checked roles state) := do
  guard (roles.length ≤ 128 && state.quantum.live.length ≤ 128 && bindings.length ≤ 128) .limit
  exactWork (Exact.charge (16*(Raw.OwnerFlow.fields roles+1)*(bindings.length+1)+
    64*(roles.length+state.quantum.live.length+bindings.length+1)^2))
  if ordered : bindings.map (·.owner) = roles then
    if ownersDistinct : (roles.map (·.ordinal)).Nodup then
      if tokensDistinct : (bindings.map (·.port.token)).Nodup then
        if complete : (bindings.map (·.port)).Perm state.quantum.live then
          return ⟨bindings,ordered,ownersDistinct,tokensDistinct,complete⟩
        else throw .request
      else throw .request
    else throw .request
  else throw .request

/-- Reorder only by independently derived logical identity. Equal-width ports
or identical basis trees cannot satisfy a missing owner. -/
def order (roles : List Owner) (bindings : Map) : WorkM Map := do
  exactWork (Exact.charge (16*(Raw.OwnerFlow.fields roles+1)*(bindings.length+1)))
  roles.mapM fun owner => do
    let some binding := byOwner bindings owner | throw .request
    return binding

theorem Checked.fullFrame {roles state} (checked : Checked roles state) :
    ∀ port ∈ state.quantum.live, ∃ binding ∈ checked.bindings, binding.port = port := by
  intro port present
  have mapped : port ∈ checked.bindings.map (·.port) := checked.complete.mem_iff.mpr present
  obtain ⟨binding,member,equal⟩ := List.mem_map.mp mapped
  exact ⟨binding,member,equal⟩

end QleisliKernel.Qirf.RuntimeOwnerMap
