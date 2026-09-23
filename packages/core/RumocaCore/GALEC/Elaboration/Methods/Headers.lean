import RumocaCore.GALEC.Elaboration.Methods.Selection

/-! Check the selected public method only after exact-one name selection.
Malformed matching headers cannot disappear from the duplicate check. This is
not complete block/lifecycle policy or validation of unselected methods. -/
namespace Rumoca.GALEC.Elaboration.Methods.Headers
open _root_.Parser

def Public (name : Token) (method : AST.Method) : Prop :=
  method.visibility = .public ∧ method.name = name ∧ method.endName = name

def select (name : Token) (methods : List AST.Method) : Option AST.Method :=
  (Rumoca.GALEC.Elaboration.Methods.Selection.select name methods).bind fun method =>
    if method.visibility = .public ∧ method.endName = name then some method else none

def Selects (name : Token) (methods : List AST.Method) (method : AST.Method) : Prop :=
  Rumoca.GALEC.Elaboration.Methods.Selection.Selects name methods method ∧ Public name method

theorem select_iff (name : Token) (methods : List AST.Method) (method : AST.Method) :
    select name methods = some method ↔ Selects name methods method := by
  simp only [select, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨selected, found, checked⟩
    split at checked
    · rename_i valid
      cases Option.some.inj checked
      have selection := (Rumoca.GALEC.Elaboration.Methods.Selection.select_iff _ _ _).mp found
      exact ⟨selection, valid.1, selection.key_eq, valid.2⟩
    · contradiction
  · rintro ⟨selected, visibility, same, ending⟩
    exact ⟨method, (Rumoca.GALEC.Elaboration.Methods.Selection.select_iff _ _ _).mpr selected,
      by simp [visibility, ending]⟩

theorem selected_original (selected : Selects name methods method) :
    method ∈ methods ∧ Public name method := ⟨selected.1.mem, selected.2⟩

theorem repeated_rejected (name : Token) (before between after : List AST.Method)
    (a b : AST.Method) (first : a.name = name) (second : b.name = name) :
    select name (before ++ [a] ++ between ++ [b] ++ after) = none := by
  simp only [select, Rumoca.GALEC.Elaboration.Methods.Selection.repeated_rejected name before between after a b first second,
    Option.bind_none]

end Rumoca.GALEC.Elaboration.Methods.Headers
