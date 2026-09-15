import RumocaFMI3.Metadata
import XML.Syntax

/-! Observations of the actual XML tree for the current tiny profile. Omitted
capabilities and absent declaration kinds are distinct facts. They do not by
themselves settle the legality of empty Clock/interval/output-derivative calls.
Schema defaults and legal call domains require their separate standards review. -/
namespace Rumoca.FMI3.CapabilityMetadata

def commonFlags : List String :=
  ["canGetAndSetFMUState", "canSerializeFMUState", "providesDirectionalDerivatives",
   "providesAdjointDerivatives", "providesPerElementDependencies"]

def InterfaceOmissions (root : XML.Element) (tag : String) (attributes : List String) : Prop :=
  ∃ node, root.children.filter (fun child => child.name == tag) = [node] ∧
    ∀ key ∈ attributes, node.attributes.lookup key = none

structure Profile (root : XML.Element) : Prop where
  me : InterfaceOmissions root "ModelExchange" commonFlags
  cs : InterfaceOmissions root "CoSimulation" (commonFlags ++ ["hasEventMode", "maxOutputDerivativeOrder"])
  scheduled : root.children.filter (fun node => node.name == "ScheduledExecution") = []
  declarations : ∃ decls, root.children.filter (fun node => node.name == "ModelVariables") = [decls] ∧
    ∀ node ∈ decls.children,
      node.name ≠ "Clock" ∧ node.attributes.lookup "causality" ≠ some "structuralParameter"

theorem described (model : Solve.FMI3Model source) : Profile (modelDescription model) := by
  refine ⟨⟨_, rfl, ?_⟩, ⟨_, rfl, ?_⟩, rfl, ⟨_, rfl, ?_⟩⟩
  · intro key member
    simp only [commonFlags, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro key member
    simp only [commonFlags, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro node member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp [List.lookup]

def Declaration (root node : XML.Element) : Prop :=
  ∃ decls, root.children.filter (fun child => child.name == "ModelVariables") = [decls] ∧
    node ∈ decls.children

theorem no_clock_or_structural_parameter (profile : Profile root) (declared : Declaration root node) :
    node.name ≠ "Clock" ∧ node.attributes.lookup "causality" ≠ some "structuralParameter" := by
  obtain ⟨decls, selected, absent⟩ := profile.declarations
  obtain ⟨other, selectedOther, member⟩ := declared
  have same : decls = other := List.singleton_inj.mp (selected.symm.trans selectedOther)
  subst other
  exact absent node member

def ArtifactContract (text : String) : Prop :=
  ∃ root, XML.Document root text ∧ root.name = "fmiModelDescription" ∧ Profile root

theorem artifact (model : Solve.FMI3Model source) (text : String)
    (document : XML.Document (modelDescription model) text) : ArtifactContract text :=
  ⟨modelDescription model, document, rfl, described model⟩

end Rumoca.FMI3.CapabilityMetadata
