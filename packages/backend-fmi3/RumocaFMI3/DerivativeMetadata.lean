import RumocaFMI3.StateMetadata

/-! The derivative vector retains the same ModelStructure entry order as the
state vector. Names are recovered from uniquely referenced XML declarations,
not from calling the metadata renderer as the interpretation relation. -/
namespace Rumoca.FMI3.DerivativeMetadata
open XML

def EntryName (nodes : List XML.Element) (entry : XML.Element) (name : String) : Prop :=
  ∃ reference declaration,
    entry.attributes.lookup "valueReference" = some reference ∧
    nodes.filter (fun node => node.attributes.lookup "valueReference" == some reference) = [declaration] ∧
    declaration.attributes.lookup "name" = some name

def DerivativeReference (nodes : List XML.Element) (entry : XML.Element) (pair : String × String) : Prop :=
  StateMetadata.StateReference nodes entry pair.1 ∧ EntryName nodes entry pair.2

def OrderedDerivatives (root : XML.Element) (pairs : List (String × String)) : Prop :=
  ∃ nodes layout,
    root.children.filter (fun node => node.name == "ModelVariables") = [nodes] ∧
    root.children.filter (fun node => node.name == "ModelStructure") = [layout] ∧
    List.Forall₂ (DerivativeReference nodes.children)
      (layout.children.filter (fun node => node.name == "ContinuousStateDerivative")) pairs

theorem EntryName.unique (first : EntryName nodes entry name) (second : EntryName nodes entry other) :
    name = other := by
  obtain ⟨reference, declaration, href, hnode, hname⟩ := first
  obtain ⟨reference', declaration', href', hnode', hname'⟩ := second
  have hr := Option.some.inj (href.symm.trans href')
  subst reference'
  have hn := List.singleton_inj.mp (hnode.symm.trans hnode')
  subst declaration'
  exact Option.some.inj (hname.symm.trans hname')

theorem DerivativeReference.unique (first : DerivativeReference nodes entry pair)
    (second : DerivativeReference nodes entry other) : pair = other :=
  Prod.ext (first.1.unique second.1) (first.2.unique second.2)

private theorem references_unique (first : List.Forall₂ (DerivativeReference nodes) entries names)
    (second : List.Forall₂ (DerivativeReference nodes) entries others) : names = others := by
  induction first generalizing others with
  | nil => cases second; rfl
  | cons head tail ih =>
    cases second with
    | cons other rest => rw [head.unique other, ih rest]

theorem OrderedDerivatives.unique (first : OrderedDerivatives root pairs)
    (second : OrderedDerivatives root others) : pairs = others := by
  obtain ⟨nodes, layout, hn, hl, ordered⟩ := first
  obtain ⟨nodes', layout', hn', hl', ordered'⟩ := second
  have ne := List.singleton_inj.mp (hn.symm.trans hn')
  subst nodes'
  have le := List.singleton_inj.mp (hl.symm.trans hl')
  subst layout'
  exact references_unique ordered ordered'

theorem OrderedDerivatives.states (ordered : OrderedDerivatives root pairs) :
    StateMetadata.OrderedStates root (pairs.map Prod.fst) := by
  obtain ⟨nodes, layout, hn, hl, related⟩ := ordered
  refine ⟨nodes, layout, hn, hl, ?_⟩
  exact List.forall₂_map_right_iff.mpr (related.imp (fun _ _ reference => reference.1))

theorem described_derivatives (model : Solve.FMI3Model source) :
    OrderedDerivatives (modelDescription model) [(source.state, model.derivativeName)] := by
  refine ⟨_, _, rfl, rfl, List.Forall₂.cons ⟨?_, ?_⟩ .nil⟩
  · exact ⟨"2", _, "1", _, rfl, rfl, ⟨rfl, rfl, rfl⟩,
      rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩⟩
  · exact ⟨"2", _, rfl, rfl, rfl⟩

def Contract (source : AST.Model) (text : String) : Prop :=
  ∃ root, XML.Document root text ∧
    OrderedDerivatives root [(source.state, "der(" ++ source.state ++ ")")]

theorem artifact_derivatives (model : Solve.FMI3Model source) (text : String)
    (metadata : XML.Document (modelDescription model) text) : Contract source text :=
  ⟨modelDescription model, metadata, described_derivatives model⟩

end Rumoca.FMI3.DerivativeMetadata
