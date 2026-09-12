import RumocaC.Tokens
import Mathlib.Data.List.Chain

/-! Ordinary-literal concatenation in C11 translation phase six (N1570
§§5.1.1.2,6.4.5). Tokens store object bytes including the final NUL, so joining
literals removes the intermediate terminator. The separated-token invariant
proves that no concatenation step can change the supplied token sequence.
Earlier preprocessing and source/execution encodings are separate obligations. -/
namespace Rumoca.CTokens.PhaseSix

def NonString : Token → Prop
  | .string _ => False
  | _ => True

def Separated (tokens : List Token) : Prop :=
  tokens.IsChain (fun a b => NonString a ∨ NonString b)

inductive Rewrite : List Token → List Token → Prop where
  | concatenate (before : List Token) (left right : List UInt8) (after : List Token) :
      Rewrite (before ++ .string left :: .string right :: after)
        (before ++ .string (left.dropLast ++ right) :: after)

theorem Separated.no_rewrite (safe : Separated input) (step : Rewrite input output) : False := by
  cases step with
  | concatenate before left right after =>
      have boundary := (List.isChain_append_cons_cons.mp safe).2.1
      exact boundary.elim id id

theorem Separated.unchanged (safe : Separated input)
    (steps : Relation.ReflTransGen Rewrite input output) : output = input := by
  induction steps with
  | refl => rfl
  | @tail middle last previous step ih =>
      subst middle
      exact False.elim (safe.no_rewrite step)

theorem Separated.empty : Separated [] := .nil
theorem Separated.single (token : Token) : Separated [token] := .singleton token

theorem Separated.prepend (safe : Separated tokens) (notString : NonString token) :
    Separated (token :: tokens) :=
  safe.cons (fun _ _ => Or.inl notString)

theorem Separated.append_separator (left : Separated before) (right : Separated after)
    (notString : NonString token) : Separated (before ++ token :: after) := by
  apply left.append (right.prepend notString)
  intro x hx y hy
  have same : y = token := (show token = y by simpa using hy).symm
  subst y
  exact Or.inr notString

theorem Separated.all_nonstring (all : ∀ token ∈ tokens, NonString token) : Separated tokens := by
  induction tokens with
  | nil => exact .empty
  | cons t ts ih => exact (ih (fun t member => all t (by simp [member]))).prepend (all t (by simp))

/-- A fragment separated internally and at its end from any separated suffix. -/
def Closed (tokens : List Token) : Prop :=
  ∀ more, Separated more → Separated (tokens ++ more)

theorem Closed.separated (closed : Closed tokens) : Separated tokens := by
  simpa using closed [] .empty

theorem Closed.empty : Closed [] := fun _ safe => safe

theorem Closed.append (left : Closed before) (right : Closed after) : Closed (before ++ after) := by
  intro more safe
  simpa only [List.append_assoc] using left _ (right _ safe)

theorem Closed.prepend (closed : Closed tokens) (notString : NonString token) : Closed (token :: tokens) := by
  intro more safe
  exact (closed _ safe).prepend notString

theorem Closed.seal (safe : Separated tokens) (notString : NonString token) : Closed (tokens ++ [token]) := by
  intro more tail
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using safe.append_separator tail notString

theorem Closed.between (left : Separated before) (right : Closed after) (notString : NonString token) :
    Closed (before ++ token :: after) := by
  intro more tail
  simpa only [List.append_assoc, List.cons_append] using left.append_separator (right _ tail) notString

theorem Closed.all_nonstring (all : ∀ token ∈ tokens, NonString token) : Closed tokens := by
  induction tokens with
  | nil => exact .empty
  | cons t ts ih => exact (ih (fun t member => all t (by simp [member]))).prepend (all t (by simp))

end Rumoca.CTokens.PhaseSix

