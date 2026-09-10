import Lean.Data.Lsp.Basic

/-! The standard uses signed integer document versions. Lean's own server types
use Nat here, so these small wire records preserve the LSP integer domain.
Only full text changes are accepted, as advertised during initialization. -/
namespace RumocaLSP.Sync
open Lean

structure Item where
  uri : String
  languageId : String
  version : Int
  text : String
  deriving FromJson

structure Open where
  textDocument : Item
  deriving FromJson

structure Versioned where
  uri : String
  version : Int
  deriving FromJson

structure FullChange where
  text : String

instance : FromJson FullChange where
  fromJson? j := do
    if (j.getObjVal? "range").isOk then throw "full text synchronization is required"
    return ⟨← j.getObjValAs? String "text"⟩

structure Change where
  textDocument : Versioned
  contentChanges : Array FullChange
  deriving FromJson

end RumocaLSP.Sync
