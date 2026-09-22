import RumocaCore.GALEC.Elaboration.IteratorNames

/-! Compiler-side assembly of named declarations. Source order is retained;
duplicates are rejected rather than resolved by silently discarding a binding.
The element classifier remains a compiler parameter, not stored in IR. -/
namespace Rumoca.GALEC.Elaboration.Declarations.NamedLists

def lower (readDeclaration : Source → Option Decl) (name : Decl → String) :
    List Source → Option (List Decl)
  | [] => some []
  | source :: sources => (readDeclaration source).bind fun declaration =>
      (lower readDeclaration name sources).bind fun declarations =>
        if name declaration ∈ declarations.map name then none
        else some (declaration :: declarations)

inductive Elaborates (Declares : Source → Decl → Prop) (name : Decl → String) :
    List Source → List Decl → Prop where
  | nil : Elaborates Declares name [] []
  | cons : Declares source declaration → Elaborates Declares name sources declarations →
      name declaration ∉ declarations.map name →
      Elaborates Declares name (source :: sources) (declaration :: declarations)

theorem lower_sound (readDeclaration : Source → Option Decl) (name : Decl → String)
    (Declares : Source → Decl → Prop)
    (correct : ∀ source declaration, readDeclaration source = some declaration ↔ Declares source declaration)
    (sources : List Source) (declarations : List Decl)
    (found : lower readDeclaration name sources = some declarations) :
    Elaborates Declares name sources declarations := by
  induction sources generalizing declarations with
  | nil =>
    cases Option.some.inj found
    exact .nil
  | cons source sources ih =>
    obtain ⟨declaration, first, accepted⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨rest, following, accepted⟩ := Option.bind_eq_some_iff.mp accepted
    split at accepted
    · contradiction
    · rename_i fresh
      cases Option.some.inj accepted
      exact .cons ((correct _ _).mp first) (ih _ following) fresh

theorem lower_complete (readDeclaration : Source → Option Decl) (name : Decl → String)
    (Declares : Source → Decl → Prop)
    (correct : ∀ source declaration, readDeclaration source = some declaration ↔ Declares source declaration)
    (elaborated : Elaborates Declares name sources declarations) :
    lower readDeclaration name sources = some declarations := by
  induction elaborated with
  | nil => rfl
  | cons declared _ fresh ih =>
    simp only [lower, (correct _ _).mpr declared, Option.bind_some, ih, if_neg fresh]

theorem lower_iff (readDeclaration : Source → Option Decl) (name : Decl → String)
    (Declares : Source → Decl → Prop)
    (correct : ∀ source declaration, readDeclaration source = some declaration ↔ Declares source declaration)
    (sources : List Source) (declarations : List Decl) :
    lower readDeclaration name sources = some declarations ↔
      Elaborates Declares name sources declarations :=
  ⟨lower_sound readDeclaration name Declares correct sources declarations,
    lower_complete readDeclaration name Declares correct⟩

theorem elaborates_iff (Declares : Source → Decl → Prop) (name : Decl → String)
    (sources : List Source) (declarations : List Decl) :
    Elaborates Declares name sources declarations ↔
      List.Forall₂ Declares sources declarations ∧ (declarations.map name).Nodup := by
  constructor
  · intro elaborated
    induction elaborated with
    | nil => exact ⟨.nil, List.nodup_nil⟩
    | cons first _ fresh ih =>
      exact ⟨.cons first ih.1, List.nodup_cons.mpr ⟨fresh, ih.2⟩⟩
  · rintro ⟨paired, unique⟩
    induction paired with
    | nil => exact .nil
    | cons first rest ih =>
      obtain ⟨fresh, tailUnique⟩ := List.nodup_cons.mp unique
      exact .cons first (ih tailUnique) fresh

theorem length_preserved (elaborated : Elaborates Declares name sources declarations) :
    sources.length = declarations.length := by
  induction elaborated with
  | nil => rfl
  | cons _ _ _ ih => exact congrArg Nat.succ ih

theorem names_unique (elaborated : Elaborates Declares name sources declarations) :
    (declarations.map name).Nodup :=
  ((elaborates_iff _ _ _ _).mp elaborated).2

end Rumoca.GALEC.Elaboration.Declarations.NamedLists
