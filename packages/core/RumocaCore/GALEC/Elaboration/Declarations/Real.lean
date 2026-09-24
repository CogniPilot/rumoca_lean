import RumocaCore.GALEC.Elaboration.Declarations.Extents
import RumocaCore.GALEC.Elaboration.Declarations.NamedLists
import GALECParser.AST
import RumocaCore.Tensor
import Mathlib.Data.List.Nodup

/-! AST-level Real declaration elaboration. Each source declaration is read
together with the block section that contains it, and the legality of its kind
in that section is checked; the kind is preserved, not interpreted as method
write permissions. The caller must still validate block/function namespaces,
scanner origins and the method-specific policy. -/
namespace Rumoca.GALEC.Elaboration.Declarations.Real
open _root_.Parser Rumoca.Tensor

structure Descriptor where
  name : String
  visibility : AST.Visibility
  kind : AST.Kind
  shape : Shape
  deriving Repr, DecidableEq

/-- Section legality of a declaration kind: a direction only in the leading
(public) section, `constant` only in the protected section. -/
def Legal : AST.Visibility → AST.Kind → Prop
  | .public, .constant => False
  | .protected, .input | .protected, .output => False
  | _, _ => True

instance (visibility : AST.Visibility) (kind : AST.Kind) : Decidable (Legal visibility kind) := by
  cases visibility <;> cases kind <;> unfold Legal <;> infer_instance

def read (ceiling : Nat) : AST.Visibility × AST.Declaration → Option Descriptor
  | (visibility, ⟨kind, .literal "Real", extents, .ident name⟩) =>
      if Legal visibility kind then
        (Extents.read ceiling extents).map fun dims => ⟨name, visibility, kind, ⟨dims⟩⟩
      else none
  | _ => none

inductive Declares (ceiling : Nat) : AST.Visibility × AST.Declaration → Descriptor → Prop where
  | real (legal : Legal visibility kind)
      (dimensions : Extents.Denotes ceiling extents dims) :
      Declares ceiling (visibility, ⟨kind, .literal "Real", extents, .ident name⟩)
        ⟨name, visibility, kind, ⟨dims⟩⟩

theorem read_iff (ceiling : Nat) (source : AST.Visibility × AST.Declaration)
    (declaration : Descriptor) :
    read ceiling source = some declaration ↔ Declares ceiling source declaration := by
  constructor
  · intro found
    obtain ⟨visibility, kind, typeName, extents, name⟩ := source
    unfold read at found
    split at found
    · rename_i same
      cases same
      split at found
      · rename_i legal
        obtain ⟨dims, lowered, same⟩ := Option.map_eq_some_iff.mp found
        cases same
        exact .real legal ((Extents.read_iff _ _ _).mp lowered)
      · contradiction
    · contradiction
  · intro declared
    cases declared with
    | real legal dimensions =>
      simp only [read, if_pos legal, (Extents.read_iff _ _ _).mpr dimensions, Option.map_some]

theorem metadata_preserved (declared : Declares ceiling source declaration) :
    source.2.name = .ident declaration.name ∧ source.2.typeName = .literal "Real" ∧
      source.1 = declaration.visibility ∧ source.2.kind = declaration.kind := by
  cases declared
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem legal_preserved (declared : Declares ceiling source declaration) :
    Legal declaration.visibility declaration.kind := by
  cases declared with
  | real legal _ => exact legal

theorem rank_preserved (declared : Declares ceiling source declaration) :
    declaration.shape.dimensions.length = source.2.rank := by
  cases declared with
  | real _ dimensions => exact Extents.rank_preserved dimensions

theorem extent_bounds (declared : Declares ceiling source declaration) :
    ∀ extent ∈ declaration.shape.dimensions, 0 < extent ∧ extent ≤ ceiling := by
  cases declared with
  | real _ dimensions => exact Extents.bounds dimensions

def readAll (ceiling : Nat) : List (AST.Visibility × AST.Declaration) → Option (List Descriptor) :=
  NamedLists.lower (read ceiling) Descriptor.name

abbrev DeclaresAll (ceiling : Nat) := NamedLists.Elaborates (Declares ceiling) Descriptor.name

theorem readAll_iff (ceiling : Nat) (sources : List (AST.Visibility × AST.Declaration)) (declarations : List Descriptor) :
    readAll ceiling sources = some declarations ↔ DeclaresAll ceiling sources declarations :=
  NamedLists.lower_iff _ _ _ (read_iff ceiling) sources declarations

theorem names_preserved (declared : DeclaresAll ceiling sources declarations) :
    sources.map (·.2.name) = declarations.map (fun declaration => Token.ident declaration.name) := by
  induction declared with
  | nil => rfl
  | cons first _ _ ih =>
    simp only [List.map_cons, (metadata_preserved first).1, ih]

theorem names_unique (declared : DeclaresAll ceiling sources declarations) :
    (declarations.map Descriptor.name).Nodup := NamedLists.names_unique declared

theorem source_names_unique (declared : DeclaresAll ceiling sources declarations) :
    (sources.map (·.2.name)).Nodup := by
  rw [names_preserved declared]
  have unique := List.Nodup.map (fun _ _ equal => Token.ident.inj equal) (names_unique declared)
  simpa only [List.map_map, Function.comp_def] using unique

end Rumoca.GALEC.Elaboration.Declarations.Real
