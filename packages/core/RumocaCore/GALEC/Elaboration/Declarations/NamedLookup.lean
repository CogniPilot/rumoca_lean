import RumocaCore.GALEC.Elaboration.Declarations.NamedLists

/-! First-match lookup agrees with membership when validated declarations have
unique names. No declaration is discarded or selected by shape compatibility. -/
namespace Rumoca.GALEC.Elaboration.Declarations.NamedLookup

def lookup (name : Decl → String) : List Decl → String → Option Decl
  | [], _ => none
  | declaration :: declarations, wanted =>
      if wanted = name declaration then some declaration else lookup name declarations wanted

theorem lookup_iff (name : Decl → String) (declarations : List Decl)
    (unique : (declarations.map name).Nodup) (wanted : String) (declaration : Decl) :
    lookup name declarations wanted = some declaration ↔
      declaration ∈ declarations ∧ name declaration = wanted := by
  induction declarations with
  | nil => simp [lookup]
  | cons head tail ih =>
    obtain ⟨fresh, tailUnique⟩ := List.nodup_cons.mp unique
    by_cases same : wanted = name head
    · simp only [lookup, if_pos same]
      constructor
      · intro found
        cases Option.some.inj found
        exact ⟨List.mem_cons_self, same.symm⟩
      · rintro ⟨member, named⟩
        cases List.mem_cons.mp member with
        | inl equal => subst declaration; rfl
        | inr member =>
          exact False.elim (fresh (List.mem_map.mpr ⟨declaration, member, named.trans same⟩))
    · simp only [lookup, if_neg same]
      constructor
      · intro found
        obtain ⟨member, named⟩ := (ih tailUnique).mp found
        exact ⟨List.mem_cons_of_mem _ member, named⟩
      · rintro ⟨member, named⟩
        cases List.mem_cons.mp member with
        | inl equal => subst declaration; exact False.elim (same named.symm)
        | inr member => exact (ih tailUnique).mpr ⟨member, named⟩

end Rumoca.GALEC.Elaboration.Declarations.NamedLookup
