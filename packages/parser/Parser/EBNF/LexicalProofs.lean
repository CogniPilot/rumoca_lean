import Parser.EBNF
import Parser.EBNF.Lexical

/-! Character-reader correctness against the independent EBNF lexical rules. -/
namespace Parser.EBNF.Reader
open Metalanguage

private theorem bind_ok {m : Except ε α} {k : α → Except ε β} {value : β}
    (result : (m >>= k) = .ok value) : ∃ x, m = .ok x ∧ k x = .ok value := by
  cases m with
  | error error => cases result
  | ok x => exact ⟨x, rfl, result⟩

private theorem quotedBody_cons : QuotedBody delimiter (char :: body) ↔
    (char ≠ delimiter ∧ char ≠ '\\') ∧ QuotedBody delimiter body := by
  simp [QuotedBody]

private theorem ofList_cons (char : Char) (body : List Char) :
    String.ofList (char :: body) = String.singleton char ++ String.ofList body := by
  rw [String.singleton_eq_ofList, ← String.ofList_append]
  rfl

theorem quoted_complete (valid : QuotedBody delimiter body) (quote : delimiter ≠ '\\') :
    quoted delimiter (body ++ delimiter :: rest) = .ok (String.ofList body, rest) := by
  induction body with
  | nil =>
    rw [List.nil_append, quoted.eq_3 delimiter delimiter rest quote]
    simp [pure, Except.pure]
  | cons char body ih =>
    obtain ⟨⟨different, escape⟩, valid⟩ := quotedBody_cons.mp valid
    have read := ih valid
    rw [List.cons_append, quoted.eq_3 _ _ _ escape]
    simp [different, read, bind, Except.bind, pure, Except.pure, ofList_cons]

theorem quoted_sound (parsed : quoted delimiter input = .ok (text, rest)) :
    ∃ body, input = body ++ delimiter :: rest ∧
      text = String.ofList body ∧ QuotedBody delimiter body := by
  induction input generalizing text with
  | nil => simp [quoted] at parsed
  | cons char chars ih =>
    by_cases escape : char = '\\'
    · subst char; simp [quoted] at parsed
    · by_cases closes : char = delimiter
      · rw [quoted.eq_3 _ _ _ escape] at parsed
        simp [closes, pure, Except.pure] at parsed
        obtain ⟨rfl, rfl⟩ := parsed
        exact ⟨[], by simp [closes], rfl, by simp [QuotedBody]⟩
      · rw [quoted.eq_3 _ _ _ escape] at parsed
        simp only [beq_iff_eq, closes, ↓reduceIte, pure_bind] at parsed
        obtain ⟨⟨suffix, following⟩, read, finish⟩ := bind_ok parsed
        have equal := Except.ok.inj finish
        have sameRest : following = rest := congrArg Prod.snd equal
        subst following
        obtain ⟨body, charsEq, textEq, bodyValid⟩ := ih read
        refine ⟨char :: body, by simp [charsEq], ?_, quotedBody_cons.mpr ⟨⟨closes, escape⟩, bodyValid⟩⟩
        have sameText := congrArg Prod.fst equal
        dsimp only at sameText
        rw [← sameText, textEq]
        exact (ofList_cons _ _).symm

theorem quoted_iff (quote : delimiter ≠ '\\') :
    quoted delimiter input = .ok (text, rest) ↔
      ∃ body, input = body ++ delimiter :: rest ∧
        text = String.ofList body ∧ QuotedBody delimiter body := by
  constructor
  · exact quoted_sound
  · rintro ⟨body, rfl, rfl, valid⟩
    exact quoted_complete valid quote

theorem comment_complete (valid : CommentBody body) :
    comment (body ++ '*' :: ')' :: rest) = .ok rest := by
  induction body with
  | nil => rfl
  | cons char body ih =>
    obtain ⟨tailValid, firstValid⟩ := commentBody_cons.mp valid
    have noEarly : ∀ tail, char = '*' → body ++ '*' :: ')' :: rest = ')' :: tail → False := by
      intro tail first equal
      apply firstValid first
      cases body with
      | nil => simp at equal
      | cons next body =>
        have : next = ')' := (List.cons.inj equal).1
        simpa using this
    rw [List.cons_append, comment.eq_3 _ _ noEarly]
    exact ih tailValid

theorem comment_sound (parsed : comment input = .ok rest) :
    ∃ body, input = body ++ '*' :: ')' :: rest ∧ CommentBody body := by
  induction input with
  | nil => simp [comment] at parsed
  | cons char chars ih =>
    by_cases closes : char = '*' ∧ chars.head? = some ')'
    · obtain ⟨rfl, head⟩ := closes
      cases chars with
      | nil => simp at head
      | cons next tail =>
        have : next = ')' := by simpa using head
        subst next
        have same := Except.ok.inj ((comment.eq_2 tail).symm.trans parsed)
        subst tail
        exact ⟨[], rfl, commentBody_nil⟩
    · have noEarly : ∀ tail, char = '*' → chars = ')' :: tail → False := by
        intro tail first equal
        exact closes ⟨first, by simp [equal]⟩
      rw [comment.eq_3 _ _ noEarly] at parsed
      obtain ⟨body, charsEq, valid⟩ := ih parsed
      refine ⟨char :: body, by simp [charsEq], commentBody_cons.mpr ⟨valid, ?_⟩⟩
      intro first head
      apply closes
      refine ⟨first, ?_⟩
      rw [charsEq]
      cases body with
      | nil => simp at head
      | cons next body => simpa using head

theorem comment_iff : comment input = .ok rest ↔
    ∃ body, input = body ++ '*' :: ')' :: rest ∧ CommentBody body := by
  constructor
  · exact comment_sound
  · rintro ⟨body, rfl, valid⟩
    exact comment_complete valid

/-- Standard-library span operations implement maximal munch for any character
class; the specification gives only membership and the next-character boundary. -/
theorem takeWhile_exact {p : α → Bool} {body rest : List α}
    (inside : ∀ value ∈ body, p value = true)
    (boundary : ∀ value, rest.head? = some value → p value = false) :
    (body ++ rest).takeWhile p = body := by
  rw [List.takeWhile_append_of_pos inside]
  have stop : rest.takeWhile p = [] := by
    cases rest with
    | nil => rfl
    | cons value tail => simp [boundary value rfl]
  simp [stop]

theorem dropWhile_exact {p : α → Bool} {body rest : List α}
    (inside : ∀ value ∈ body, p value = true)
    (boundary : ∀ value, rest.head? = some value → p value = false) :
    (body ++ rest).dropWhile p = rest := by
  rw [List.dropWhile_append_of_pos inside]
  cases rest with
  | nil => rfl
  | cons value tail => simp [boundary value rfl]

theorem name_complete (valid : NameBody first tail rest) :
    (first :: (tail ++ rest)).takeWhile identRest = first :: tail ∧
      (first :: (tail ++ rest)).drop (first :: tail).length = rest := by
  have inside : ∀ value ∈ first :: tail, identRest value = true := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · simp [identRest, valid.1]
    · exact valid.2.1 value member
  exact ⟨takeWhile_exact inside valid.2.2, by simp⟩

theorem line_complete (inside : '\n' ∉ body)
    (boundary : rest = [] ∨ rest.head? = some '\n') :
    ('/' :: '/' :: (body ++ rest)).dropWhile (· != '\n') = rest := by
  have bodyChars : ∀ value ∈ '/' :: '/' :: body, (value != '\n') = true := by
    intro value member
    simp only [List.mem_cons] at member
    rcases member with rfl | rfl | member
    · decide
    · decide
    · have different : value ≠ '\n' := by intro equal; subst value; exact inside member
      simpa using different
  apply dropWhile_exact bodyChars
  intro value head
  rcases boundary with rfl | boundary
  · simp at head
  · have : value = '\n' := Option.some.inj (head.symm.trans boundary)
    simp [this]

end Parser.EBNF.Reader
