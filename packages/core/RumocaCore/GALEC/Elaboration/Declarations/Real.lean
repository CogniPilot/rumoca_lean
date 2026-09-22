import RumocaCore.GALEC.Elaboration.Declarations.Extents
import RumocaCore.GALEC.Elaboration.Declarations.NamedLists
import GALECParser.AST
import RumocaCore.Tensor
import Mathlib.Data.List.Nodup

/-! AST-level Real declaration elaboration. Syntax metadata is preserved,
not interpreted as method write permissions. The caller must still validate
block/function namespaces, scanner origins and the method-specific policy. -/
namespace Rumoca.GALEC.Elaboration.Declarations.Real
open _root_.Parser Rumoca.Tensor

structure Descriptor where
  name : String
  visibility : AST.Visibility
  direction : AST.Direction
  variability : AST.Variability
  shape : Shape
  deriving Repr, DecidableEq

def read (ceiling : Nat) (source : AST.Declaration) : Option Descriptor :=
  match source.name, source.typeName with
  | .ident name, .literal "Real" => (Extents.read ceiling source.extents).map fun dims =>
      ⟨name, source.visibility, source.direction, source.variability, ⟨dims⟩⟩
  | _, _ => none

inductive Declares (ceiling : Nat) : AST.Declaration → Descriptor → Prop where
  | real (dimensions : Extents.Denotes ceiling extents dims) :
      Declares ceiling ⟨visibility, direction, variability, .literal "Real", extents, .ident name⟩
        ⟨name, visibility, direction, variability, ⟨dims⟩⟩

theorem read_iff (ceiling : Nat) (source : AST.Declaration) (declaration : Descriptor) :
    read ceiling source = some declaration ↔ Declares ceiling source declaration := by
  constructor
  · intro found
    cases source with
    | mk visibility direction variability typeName extents name =>
      unfold read at found
      dsimp only at found
      split at found
      · obtain ⟨dims, lowered, same⟩ := Option.map_eq_some_iff.mp found
        cases same
        exact .real ((Extents.read_iff _ _ _).mp lowered)
      · contradiction
  · intro declared
    cases declared with
    | real dimensions =>
      simp only [read, (Extents.read_iff _ _ _).mpr dimensions, Option.map_some]

theorem metadata_preserved (declared : Declares ceiling source declaration) :
    source.name = .ident declaration.name ∧ source.typeName = .literal "Real" ∧
      source.visibility = declaration.visibility ∧ source.direction = declaration.direction ∧
      source.variability = declaration.variability := by
  cases declared
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem rank_preserved (declared : Declares ceiling source declaration) :
    declaration.shape.dimensions.length = source.rank := by
  cases declared with
  | real dimensions => exact Extents.rank_preserved dimensions

theorem extent_bounds (declared : Declares ceiling source declaration) :
    ∀ extent ∈ declaration.shape.dimensions, 0 < extent ∧ extent ≤ ceiling := by
  cases declared with
  | real dimensions => exact Extents.bounds dimensions

def readAll (ceiling : Nat) : List AST.Declaration → Option (List Descriptor) :=
  NamedLists.lower (read ceiling) Descriptor.name

abbrev DeclaresAll (ceiling : Nat) := NamedLists.Elaborates (Declares ceiling) Descriptor.name

theorem readAll_iff (ceiling : Nat) (sources : List AST.Declaration) (declarations : List Descriptor) :
    readAll ceiling sources = some declarations ↔ DeclaresAll ceiling sources declarations :=
  NamedLists.lower_iff _ _ _ (read_iff ceiling) sources declarations

theorem names_preserved (declared : DeclaresAll ceiling sources declarations) :
    sources.map AST.Declaration.name = declarations.map (fun declaration => Token.ident declaration.name) := by
  induction declared with
  | nil => rfl
  | cons first _ _ ih =>
    simp only [List.map_cons, (metadata_preserved first).1, ih]

theorem names_unique (declared : DeclaresAll ceiling sources declarations) :
    (declarations.map Descriptor.name).Nodup := NamedLists.names_unique declared

theorem source_names_unique (declared : DeclaresAll ceiling sources declarations) :
    (sources.map AST.Declaration.name).Nodup := by
  rw [names_preserved declared]
  have unique := List.Nodup.map (fun _ _ equal => Token.ident.inj equal) (names_unique declared)
  simpa only [List.map_map, Function.comp_def] using unique

end Rumoca.GALEC.Elaboration.Declarations.Real
