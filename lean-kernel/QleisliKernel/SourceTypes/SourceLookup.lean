import QleisliKernel.SourceTypes.Declarations

/-! Original lookup with explicit absence, for later source-call resolution.
An absent declaration differs from a missing module, declaration-scanner error
or ambiguous binding. The shared catalogue is not full program validation.
For example, `fn other(` can yield an absent `h` despite its incomplete header.
This component supplies no primitive/prelude fallback or lexical-scope
permission by itself; callers must bind the complete original occurrence.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceLookup
open QleisliKernel.SourceTypes

structure Checked (sources : Sources) (owner name : String) where
  source : String
  items : List Declaration
  binding : Option Declaration
  originalModule : sources.toList.filter (fun row => row.1 == owner) = [(owner,source)]
  originalItems : declarations source = .ok items
  matching : items.filter (fun item => item.name == name) = binding.toList

/-- A source row and its complete declaration scan are retained even for
absence. A caller must account for this original row in graph relevance. -/
def read (sources : Sources) (owner name : String) : Except String (Checked sources owner name) := do
  match rows : sources.toList.filter (fun row => row.1 == owner) with
  | [(moduleName,source)] =>
    if same : moduleName = owner then
      match parsed : declarations source with
      | .error error => throw error
      | .ok items =>
        let selected := items.filter (fun item => item.name == name)
        let binding ← match selected with
          | [] => pure none
          | [item] => pure (some item)
          | _ => throw "ambiguous original source declaration"
        if matching : selected = binding.toList then
          return ⟨source,items,binding,by simpa only [same] using rows,parsed,matching⟩
        else throw "original source lookup lost its selection"
    else throw "original source row name differs"
  | _ => throw "missing/ambiguous original source module"

theorem Checked.absent {sources owner name} (checked : Checked sources owner name)
    (missing : checked.binding = none) :
    checked.items.filter (fun item => item.name == name) = [] := by
  simpa only [missing,Option.toList_none] using checked.matching

/-- A successful declaration result is exactly the existing resolver's
original lookup, with no different category, source row or visibility grant. -/
theorem Checked.present {sources owner name} (checked : Checked sources owner name)
    (declaration : Declaration) (found : checked.binding = some declaration) :
    originalBinding sources owner name = .ok (checked.source,declaration) := by
  simp only [originalBinding,checked.originalModule,checked.originalItems,bind,Except.bind,
    checked.matching,found,Option.toList_some]
  rfl

theorem Checked.absent_original {sources owner name} (checked : Checked sources owner name)
    (missing : checked.binding = none) :
    originalBinding sources owner name = .error "missing/ambiguous original type declaration" := by
  simp only [originalBinding,checked.originalModule,checked.originalItems,bind,Except.bind,
    checked.matching,missing,Option.toList_none]
  rfl

end QleisliKernel.SourceTypes.SourceLookup
