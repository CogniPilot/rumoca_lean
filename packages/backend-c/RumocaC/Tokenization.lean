import RumocaC.TokenMaximal

/-! Every compositional token judgment refines the independent normal-context
tokenization specification, with the same input, token value and continuation.
Comments are excluded at token boundaries; literal contents remain intact. -/
namespace Rumoca.CTokens
open Competition

theorem Normal.CommentStart.head (comment : Normal.CommentStart input) :
    Starts (fun c => c = '/') input := by
  obtain ⟨tail, same | same⟩ := comment <;> subst input <;> exact ⟨_, _, rfl, rfl⟩

private theorem start_excludes_comment (start : Starts allowed input)
    (slash : ¬ allowed '/') : ¬ Normal.CommentStart input := by
  intro comment
  exact start.disjoint comment.head (by intro c valid same; subst c; exact slash valid)

theorem word_no_comment (word : Consumes input (.word name) rest) :
    ¬ Normal.CommentStart input :=
  start_excludes_comment (word_starts word) (by decide +kernel)

theorem number_no_comment (number : Consumes input (.number spelling) rest) :
    ¬ Normal.CommentStart input :=
  start_excludes_comment (number_input_starts number).first (by decide +kernel)

theorem string_no_comment (string : Consumes input (.string bytes) rest) :
    ¬ Normal.CommentStart input :=
  start_excludes_comment (string_input_starts string) (by decide +kernel)

theorem punctuator_no_comment (punctuation : Consumes input (.punctuator spelling) rest) :
    ¬ Normal.CommentStart input := by
  cases punctuation with
  | punctuator read safe =>
      intro comment
      have catalog : ∀ word ∈ CPunctuator.spellings,
          word.toList.head? = some '/' → word = "/" ∨ word = "/=" := by decide +kernel
      obtain ⟨first, tail, chars, valid⟩ := punctuator_starts read.member
      have firstSlash := comment.head
      rw [read.text, chars] at firstSlash
      have slash : first = '/' := firstSlash.head
      have head : spelling.toList.head? = some '/' := by simp [chars, slash]
      rcases catalog spelling read.member head with rfl | rfl
      · obtain ⟨tail, same | same⟩ := comment
        · have restEq : rest = '/' :: tail := by simpa [read.text] using same
          exact (safe.2 rfl '/' tail restEq).1 rfl
        · have restEq : rest = '*' :: tail := by simpa [read.text] using same
          exact (safe.2 rfl '*' tail restEq).2 rfl
      · obtain ⟨tail, same | same⟩ := comment <;> simp [read.text] at same

/-- Cross-category maximality, comment exclusion and spelling/value preservation
are derived from the original token proof, rather than assumed by the printer. -/
theorem Consumes.normal (token : Consumes input value rest) : Normal.Consumes input value rest := by
  cases token with
  | word parts read safe =>
      have actual : Consumes input (.word _) rest := .word parts read safe
      exact ⟨_, .word parts, read.input_eq, word_longest actual, word_no_comment actual⟩
  | number spelled same longest =>
      have actual : Consumes input (.number _) rest := .number spelled same longest
      exact ⟨_, .number spelled, same, number_longest actual, number_no_comment actual⟩
  | string literal same =>
      exact ⟨_, .string literal, same, string_longest literal same, string_no_comment (.string literal same)⟩
  | punctuator read safe =>
      have actual : Consumes input (.punctuator _) rest := .punctuator read safe
      exact ⟨_, .punctuator read.member, read.text, punctuator_longest actual, punctuator_no_comment actual⟩

theorem Prefix.normal (lexical : Prefix input tokens rest) : Normal.Prefix input tokens rest := by
  induction lexical with
  | done => exact .done
  | space white remaining ih => exact .space white ih
  | token consumed remaining ih => exact .token consumed.normal ih

theorem Lexes.normal (lexical : Lexes input tokens) : Normal.Lexes input tokens := Prefix.normal lexical

end Rumoca.CTokens
