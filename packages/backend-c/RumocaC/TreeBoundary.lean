import RumocaC.Identifier
import RumocaC.Punctuator
import Init.Data.Nat.ToString

/-! Reusable outer lexical boundaries of CTree expressions. Identifier spelling
is checked separately from type spellings, scopes and C typing. These results
do not establish complete expression tokenization or execution. -/
namespace Rumoca.CTree.Syntax
open _root_.Parser

/-- Lexical validity of expression identifiers, with typedef spellings supplied
by the surrounding context. Member names use the separate C member namespace.
This predicate deliberately says nothing about raw type spellings. -/
def IdentifierInputs (typedefs : List String) : Expr → Prop
  | .id name => CIdentifier.valid typedefs name = true
  | .nat _ | .str _ | .sizeof _ => True
  | .bin _ a b | .index a b => IdentifierInputs typedefs a ∧ IdentifierInputs typedefs b
  | .not a | .deref a | .address a | .cast _ a => IdentifierInputs typedefs a
  | .field a name _ => IdentifierInputs typedefs a ∧ CIdentifier.valid [] name = true
  | .call fn args => IdentifierInputs typedefs fn ∧ ∀ arg ∈ args, IdentifierInputs typedefs arg

/-- An expression starts with a word character, an opening parenthesis or
an ordinary string quote. This is weaker than expression lexical validity. -/
def OperandStart (text : List Char) : Prop :=
  ∃ first rest, text = first :: rest ∧
    (identRest first = true ∨ first = '(' ∨ first = '"')

theorem OperandStart.append (start : OperandStart text) (rest : List Char) :
    OperandStart (text ++ rest) := by
  obtain ⟨c, cs, rfl, allowed⟩ := start
  exact ⟨c, cs ++ rest, rfl, allowed⟩

private theorem identifier_start (valid : CIdentifier.valid typedefs name = true) :
    OperandStart name.toList := by
  obtain ⟨c, cs, text, starts, _⟩ := CIdentifier.word_parts typedefs name valid
  exact ⟨c, cs, text, Or.inl (by simp [identRest, starts])⟩

private theorem natural_start (n : Nat) : OperandStart (toString n).toList := by
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList]
  have nonempty := Nat.length_toDigits_pos (b := 10) (n := n)
  cases chars : Nat.toDigits 10 n with
  | nil => simp [chars] at nonempty
  | cons c cs =>
      have digit := Nat.isDigit_of_mem_toDigits (b := 10) (n := n)
        (by decide +kernel) (by decide +kernel) (by rw [chars]; exact List.mem_cons_self)
      exact ⟨c, cs, rfl, Or.inl (by simp [identRest, digit])⟩

/-- The actual expression renderer has a safe leading character whenever its
identifier leaves have valid C spellings. No finite list of expressions is used. -/
theorem expression_start (expr : Expr) (valid : IdentifierInputs typedefs expr) :
    OperandStart expr.render.toList := by
  induction expr using Expr.rec (motive_2 := fun _ => True) with
  | id name =>
      simpa only [Expr.render] using identifier_start
        (name := name) (by simpa only [IdentifierInputs] using valid)
  | nat n => simpa only [Expr.render] using natural_start n
  | str s =>
      simp only [Expr.render, quote, String.toList_append]
      exact ⟨'"', _, rfl, Or.inr (Or.inr rfl)⟩
  | bin op a b ha hb | not a ha | deref a ha | address a ha
  | field a name pointer ha | cast type a ha =>
      simp only [Expr.render, String.toList_append]
      exact ⟨'(', _, rfl, Or.inr (Or.inl rfl)⟩
  | sizeof type =>
      simp only [Expr.render, String.toList_append]
      exact ⟨'s', _, rfl, Or.inl (by decide +kernel)⟩
  | index a i ha hi =>
      simp only [IdentifierInputs] at valid
      simpa only [Expr.render, String.toList_append, List.append_assoc] using
        (ha valid.1).append ("[".toList ++ i.render.toList ++ "]".toList)
  | call fn args hf ha =>
      simp only [IdentifierInputs] at valid
      simpa only [Expr.render, String.toList_append, List.append_assoc] using
        (hf valid.1).append
          ("(".toList ++ (String.intercalate ", " (args.map Expr.render)).toList ++ ")".toList)
  | nil => trivial
  | cons _ _ _ _ => trivial

/-- Prefixing any C11 punctuator to a rendered operand cannot lengthen that
punctuator. This includes the actual !, * and & unary renderer boundaries. -/
theorem punctuator_before_expression (member : spelling ∈ CPunctuator.spellings)
    (expr : Expr) (valid : IdentifierInputs typedefs expr) (rest : List Char) :
    CPunctuator.Consumes (spelling.toList ++ expr.render.toList ++ rest)
      spelling (expr.render.toList ++ rest) := by
  obtain ⟨c, cs, text, first⟩ := expression_start expr valid
  rw [text, List.append_assoc, List.cons_append]
  rcases first with word | delimiter
  · exact CPunctuator.consumes_before_word member word (cs ++ rest)
  · exact CPunctuator.consumes_before_operand member delimiter (cs ++ rest)

end Rumoca.CTree.Syntax
