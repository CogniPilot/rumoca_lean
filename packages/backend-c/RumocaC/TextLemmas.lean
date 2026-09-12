import Std

/-! Shared facts about the standard-library text combinators used by C printers.
Kept separate from runtime syntax and target-specific printer certificates. -/
namespace Rumoca.CText

theorem intercalate_one (separator value : String) :
    String.intercalate separator [value] = value := rfl

theorem intercalate_cons (separator first second : String) (rest : List String) :
    String.intercalate separator (first :: second :: rest) =
      first ++ separator ++ String.intercalate separator (second :: rest) := by
  have go : ∀ rest : List String, ∀ lead acc : String,
      String.intercalate separator ((lead ++ acc) :: rest) =
        lead ++ String.intercalate separator (acc :: rest) := by
    intro rest
    induction rest with
    | nil => intros; rfl
    | cons s ss ih =>
      intro lead acc
      change String.intercalate separator (((lead ++ acc) ++ separator ++ s) :: ss) =
        lead ++ String.intercalate separator ((acc ++ separator ++ s) :: ss)
      simpa only [String.append_assoc] using ih lead (acc ++ separator ++ s)
  exact go rest (first ++ separator) second

end Rumoca.CText
