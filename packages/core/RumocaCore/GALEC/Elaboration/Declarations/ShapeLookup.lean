import RumocaCore.GALEC.Elaboration.Declarations.Real
import RumocaCore.GALEC.Elaboration.Declarations.NamedLookup
import RumocaCore.GALEC.Elaboration.Static.Bounded

/-! Declared shape lookup for the flat state-entity profile. This connects the
actual AST declarations to the existing generic dimension-query semantics;
runtime values, method permissions and backends do not participate. -/
namespace Rumoca.GALEC.Elaboration.Declarations.ShapeLookup
open Real Rumoca.Tensor

theorem declared_member_iff (declared : DeclaresAll ceiling sources declarations)
    (declaration : Descriptor) :
    declaration ∈ declarations ↔
      ∃ source ∈ sources, Declares ceiling source declaration := by
  induction declared with
  | nil => simp
  | @cons source head sources declarations first rest fresh ih =>
    constructor
    · intro member
      cases List.mem_cons.mp member with
      | inl equal => subst declaration; exact ⟨source, List.mem_cons_self, first⟩
      | inr member =>
        obtain ⟨other, present, meaning⟩ := ih.mp member
        exact ⟨other, List.mem_cons_of_mem _ present, meaning⟩
    · rintro ⟨other, present, meaning⟩
      cases List.mem_cons.mp present with
      | inl equal =>
        subst other
        have same := Option.some.inj
          (((Real.read_iff _ _ _).mpr first).symm.trans
            ((Real.read_iff _ _ _).mpr meaning))
        subst declaration
        exact List.mem_cons_self
      | inr present => exact List.mem_cons_of_mem _ (ih.mpr ⟨other, present, meaning⟩)

def read (declarations : List Descriptor) : List String → Option Shape
  | [name] => (NamedLookup.lookup Descriptor.name declarations name).map Descriptor.shape
  | _ => none

/-- Source declaration meaning, independent of descriptor-list lookup. -/
def HasShape (ceiling : Nat) (sources : List AST.Declaration) (key : List String) (shape : Shape) : Prop :=
  ∃ source ∈ sources, ∃ declaration, Declares ceiling source declaration ∧
    key = [declaration.name] ∧ shape = declaration.shape

theorem shape_bounds (known : HasShape ceiling sources key shape) :
    ∀ extent ∈ shape.dimensions, 0 < extent ∧ extent ≤ ceiling := by
  obtain ⟨source, _, declaration, meaning, _, rfl⟩ := known
  exact Real.extent_bounds meaning

theorem read_iff (declared : DeclaresAll ceiling sources declarations)
    (key : List String) (shape : Shape) :
    read declarations key = some shape ↔ HasShape ceiling sources key shape := by
  constructor
  · intro found
    unfold read at found
    split at found
    · rename_i name
      obtain ⟨declaration, located, same⟩ := Option.map_eq_some_iff.mp found
      obtain ⟨member, named⟩ :=
        (NamedLookup.lookup_iff _ _ (Real.names_unique declared) _ _).mp located
      obtain ⟨source, present, meaning⟩ := (declared_member_iff declared declaration).mp member
      exact ⟨source, present, declaration, meaning, by rw [named], same.symm⟩
    · contradiction
  · rintro ⟨source, present, declaration, meaning, rfl, rfl⟩
    have member := (declared_member_iff declared declaration).mpr ⟨source, present, meaning⟩
    have found := (NamedLookup.lookup_iff _ _ (Real.names_unique declared) _ _).mpr ⟨member, rfl⟩
    simp only [read, found, Option.map_some]

/-- The existing all-reference/axis theorem now has a provider derived from
validated source declarations rather than an unconstrained shape table. -/
theorem dimension_read_iff (declared : DeclaresAll ceiling sources declarations)
    (source : AST.Reference) (axis extent : Nat) :
    Elaboration.Static.Dimensions.read (read declarations) source axis = some extent ↔
      Elaboration.Static.Dimensions.Denotes (HasShape ceiling sources) source axis extent :=
  Elaboration.Static.Dimensions.read_iff _ _ (read_iff declared) source axis extent

theorem bounded_read_iff (declared : DeclaresAll ceiling sources declarations)
    (source : AST.Expr) (value : Nat) :
    Elaboration.Static.Bounded.read (read declarations) ceiling source = some value ↔
      Elaboration.Static.Bounded.Evaluates (HasShape ceiling sources) ceiling source value :=
  Elaboration.Static.Bounded.read_iff _ _ (read_iff declared) ceiling source value

end Rumoca.GALEC.Elaboration.Declarations.ShapeLookup
