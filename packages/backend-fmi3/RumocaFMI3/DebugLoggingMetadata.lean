import RumocaFMI3.DebugLoggingLoop
import RumocaFMI3.Metadata
import RumocaC.StringLiteralContents
import XML.Syntax

/-! The single logging flag is justified by the actual XML declaring exactly
one category. Legal FMI requests additionally require NULL for an empty list;
defensive acceptance of other represented calls is a separate C-body result. -/
namespace Rumoca.FMI3.DebugLogging
open CMemory CStringMemory

def OnlyCategory (root : XML.Element) (name : String) : Prop :=
  ∃ categories entry,
    root.children.filter (fun child => child.name == "LogCategories") = [categories] ∧
    categories.children = [entry] ∧ entry.name = "Category" ∧
    entry.attributes.lookup "name" = some name

def MetadataContract (text name : String) : Prop :=
  ∃ root, XML.Document root text ∧ root.name = "fmiModelDescription" ∧ OnlyCategory root name

theorem described_category (model : Solve.FMI3Model source) :
    OnlyCategory (modelDescription model) "logStatus" := by
  exact ⟨_, _, rfl, rfl, rfl, rfl⟩

theorem artifact_category (model : Solve.FMI3Model source) (text : String)
    (document : XML.Document (modelDescription model) text) : MetadataContract text "logStatus" :=
  ⟨modelDescription model, document, rfl, described_category model⟩

/-- Caller validity is independent of the emitted validation loop. The array
and strings still require separate readable-memory evidence for C execution. -/
def LegalRequest (pointer : Option Address) (n : Nat) (selected : Nat → Option Address)
    (bytes : Nat → List UInt8) (declared : List String) : Prop :=
  (n = 0 → pointer = none) ∧ (0 < n → pointer.isSome = true) ∧
  ∀ i < n, (selected i).isSome = true ∧ bytes i ∈ declared.map content

theorem legal_single_accepted
    (legal : LegalRequest pointer n selected bytes [name]) :
    ∀ i < n, Accepted (selected i) (bytes i) (content name) := by
  intro i inside
  obtain ⟨present, member⟩ := legal.2.2 i inside
  exact ⟨present, by simpa using member⟩

theorem legal_empty_null
    (legal : LegalRequest pointer 0 selected bytes declared) : pointer = none := legal.1 rfl

end Rumoca.FMI3.DebugLogging
