import RumocaFMI3.Float64Read
import RumocaFMI3.Metadata

namespace Rumoca.FMI3.Float64Metadata
open XML

/-- Decimal value of a nonempty ASCII digit sequence. This metadata judgment
admits leading zeroes, excludes Lean's underscore separators, and does not
claim the complete XML Schema unsignedInt lexical space. -/
def decimal (text : String) : Option Nat :=
  let chars := text.toList
  if chars ≠ [] ∧ chars.all Char.isDigit then
    some (chars.foldl (fun value c => 10 * value + (c.toNat - '0'.toNat)) 0)
  else none

def referenceOf (node : Element) : Option Nat :=
  (node.attributes.lookup "valueReference").bind decimal

/-- Independent numeric reference resolution; ModelVariables order is not the
order of an API request. Only scalar continuous Float64 declarations are in
this contract. Complete schema/capability conformance remains separate. -/
def Lookup (root : Element) (reference : Nat) (name : String) : Prop :=
  ∃ modelVariables declaration,
    root.children.filter (fun node => node.name == "ModelVariables") = [modelVariables] ∧
    modelVariables.children.filter (fun node => referenceOf node == some reference) = [declaration] ∧
    declaration.name = "Float64" ∧
    declaration.attributes.lookup "name" = some name ∧
    declaration.attributes.lookup "variability" = some "continuous" ∧
    declaration.children.filter (fun node => node.name == "Dimension") = []

theorem Lookup.unique (first : Lookup root reference name) (second : Lookup root reference other) : name = other := by
  obtain ⟨modelVariables, declaration, hv, hd, _, hn, _⟩ := first
  obtain ⟨modelVariables', declaration', hv', hd', _, hn', _⟩ := second
  have vars := List.singleton_inj.mp (hv.symm.trans hv')
  subst modelVariables'
  have decl := List.singleton_inj.mp (hd.symm.trans hd')
  subst declaration'
  exact Option.some.inj (hn.symm.trans hn')

def name (model : Solve.FMI3Model source) : Float64Calls.Variable → String
  | .time => model.timeName
  | .state => model.stateName
  | .derivative => model.derivativeName

theorem described_variable (model : Solve.FMI3Model source) (selected : Float64Calls.Variable) :
    Lookup (modelDescription model) selected.code (name model selected) := by
  let vars := (modelDescription model).children[4]'(by simp [modelDescription])
  cases selected
  · refine ⟨vars, vars.children[0]'(by simp [vars, modelDescription]), rfl, ?_, rfl, rfl, rfl, rfl⟩
    rfl
  · refine ⟨vars, vars.children[1]'(by simp [vars, modelDescription]), rfl, ?_, rfl, rfl, rfl, rfl⟩
    rfl
  · refine ⟨vars, vars.children[2]'(by simp [vars, modelDescription]), rfl, ?_, rfl, rfl, rfl, rfl⟩
    rfl

/-- The actual three declarations contain no additional value reference. -/
theorem described_reference (model : Solve.FMI3Model source) (reference : Nat) :
    (∃ variableName, Lookup (modelDescription model) reference variableName) ↔ reference ≤ 2 := by
  have enough : 4 < (modelDescription model).children.length := by simp [modelDescription]
  constructor
  · rintro ⟨variableName, modelVariables, declaration, hv, hd, _⟩
    have vars : modelVariables = (modelDescription model).children[4] := by
      exact (List.singleton_inj.mp hv).symm
    subst modelVariables
    have member : declaration ∈ (modelDescription model).children[4].children := by
      apply List.mem_of_mem_filter
      rw [hd]
      simp
    have selected : referenceOf declaration = some reference := by
      have inside : declaration ∈ (modelDescription model).children[4].children.filter
          (fun node => referenceOf node == some reference) := by rw [hd]; simp
      exact beq_iff_eq.mp (List.mem_filter.mp inside).2
    simp only [modelDescription, List.getElem_cons_zero, List.getElem_cons_succ,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · change some 0 = some reference at selected
      have same := Option.some.inj selected
      omega
    · change some 1 = some reference at selected
      have same := Option.some.inj selected
      omega
    · change some 2 = some reference at selected
      have same := Option.some.inj selected
      omega
  · intro valid
    have cases : reference = 0 ∨ reference = 1 ∨ reference = 2 := by omega
    rcases cases with rfl | rfl | rfl
    · exact ⟨_, described_variable model .time⟩
    · exact ⟨_, described_variable model .state⟩
    · exact ⟨_, described_variable model .derivative⟩

def Contract (model : Solve.FMI3Model source) (text : String) : Prop :=
  ∃ root, XML.Document root text ∧
    (∀ selected, Lookup root selected.code (name model selected)) ∧
    (∀ reference, (∃ variableName, Lookup root reference variableName) ↔ reference ≤ 2)

theorem artifact_variables (model : Solve.FMI3Model source) (text : String)
    (metadata : XML.Document (modelDescription model) text) : Contract model text :=
  ⟨modelDescription model, metadata, described_variable model, described_reference model⟩

end Rumoca.FMI3.Float64Metadata
