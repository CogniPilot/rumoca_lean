import RumocaFMI3.AbsentVariables
import RumocaFMI3.Metadata
import XML.Syntax

namespace Rumoca.FMI3.AbsentVariables

/-- FMI 3.0.2 §2.2.7.2 also assigns Enumeration to the Int64 API. -/
def VariableType.declarationNames : VariableType → List String
  | .int64 => ["Int64", "Enumeration"]
  | ty => [ty.name]

/-- Absence is established in the unique actual ModelVariables element. -/
def Absent (root : XML.Element) (ty : VariableType) : Prop :=
  ∃ declarations, root.children.filter (fun node => node.name == "ModelVariables") = [declarations] ∧
    declarations.children.filter (fun node => ty.declarationNames.contains node.name) = []

def Declaration (root : XML.Element) (ty : VariableType) (node : XML.Element) : Prop :=
  ∃ declarations, root.children.filter (fun child => child.name == "ModelVariables") = [declarations] ∧
    node ∈ declarations.children ∧ node.name ∈ ty.declarationNames

theorem Absent.no_declaration (absent : Absent root ty) : ¬ Declaration root ty node := by
  obtain ⟨declarations, selected, empty⟩ := absent
  rintro ⟨other, selectedOther, member, type⟩
  have same : declarations = other := List.singleton_inj.mp (selected.symm.trans selectedOther)
  subst other
  have found : node ∈ declarations.children.filter (fun node => ty.declarationNames.contains node.name) :=
    List.mem_filter.mpr ⟨member, List.contains_iff_mem.mpr type⟩
  rw [empty] at found
  exact List.not_mem_nil found

/-- Any list of correctly typed declarations is empty when this API's XML
types are absent. This includes Int64's Enumeration alias. -/
theorem Absent.selection_empty (absent : Absent root ty) (selected : List XML.Element)
    (declared : ∀ node ∈ selected, Declaration root ty node) : selected = [] := by
  cases selected with
  | nil => rfl
  | cons node rest => exact (absent.no_declaration (declared node (by simp))).elim

theorem described_absence (model : Solve.FMI3Model source) (ty : VariableType) :
    Absent (modelDescription model) ty := by
  refine ⟨(modelDescription model).children[4]'(by simp [modelDescription]), rfl, ?_⟩
  cases ty <;> rfl

def MetadataContract (text : String) : Prop :=
  ∃ root, XML.Document root text ∧ root.name = "fmiModelDescription" ∧ ∀ ty, Absent root ty

theorem artifact_absence (model : Solve.FMI3Model source) (text : String)
    (document : XML.Document (modelDescription model) text) : MetadataContract text :=
  ⟨modelDescription model, document, rfl, described_absence model⟩

end Rumoca.FMI3.AbsentVariables
