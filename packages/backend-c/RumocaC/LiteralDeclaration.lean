import RumocaC.LiteralPoolStorage

/-! Independent declaration syntax for named static character arrays. C11
N1570 6.7.9 paragraphs 14 and 22 initialize the complete unknown-size array,
including the terminating zero. This declaration-level preparation is not a
translation-unit, native-layout or whole-adapter certificate. -/
namespace Rumoca.CLiteral.Declaration
open _root_.Parser CMemory
variable {reserved : List String}

def config : Scanner.Config where
  wordStart := identStart
  wordRest := identRest
  numberRest := identRest
  classify := Token.literal
  single := fun c => ['[', ']', '=', ';'].contains c
  pair := fun _ => none

/-- The syntax specifies tokens independently of the renderer, and literal
bytes independently of the source String or symbolic memory construction. -/
def Denotes (reserved : List String) (source : List Char) (name : String)
    (object : List UInt8) : Prop :=
  CIdentifier.valid reserved name = true ∧
  ∃ lead literal suffix,
    source = lead ++ literal ++ suffix ∧
    Scanner.Lexes config lead
      (["static", "const", "char", name, "[", "]", "="].map Token.literal) ∧
    CString.Denotes literal object ∧
    Scanner.Lexes config suffix [.literal ";"]

def render (entry : Entry) : String :=
  "static const char " ++ entry.name ++ "[] = " ++ CTree.quote entry.text ++ ";"

private theorem member_dropWhile {text : List Char} (p : Char → Bool) (rejected : p c = false)
    (member : c ∈ text) : c ∈ text.dropWhile p := by
  rw [← List.takeWhile_append_dropWhile (p := p) (l := text)] at member
  rcases List.mem_append.mp member with taken | dropped
  · have accepted := List.all_eq_true.mp (List.all_takeWhile (p := p) (l := text)) c taken
    rw [rejected] at accepted
    contradiction
  · exact dropped

private theorem lex_no_quote (lexed : Scanner.Lexes config text tokens) : '"' ∉ text := by
  induction lexed with
  | nil => simp
  | @space c cs ts space tail ih =>
      intro member
      rcases List.mem_cons.mp member with rfl | member
      · contradiction
      · exact ih member
  | @word c cs ts space start tail ih =>
      intro member
      rcases List.mem_cons.mp member with rfl | member
      · contradiction
      · exact ih (member_dropWhile config.wordRest (by decide +kernel) member)
  | @number c cs ts space start digit tail ih =>
      intro member
      rcases List.mem_cons.mp member with rfl | member
      · contradiction
      · exact ih (member_dropWhile config.numberRest (by decide +kernel) member)
  | @symbol c cs t rest ts space start digit symbol tail ih =>
      cases symbol with
      | single pair allowed =>
          intro member
          rcases List.mem_cons.mp member with rfl | member
          · contradiction
          · exact ih member
      | pair pair => contradiction

private theorem before_quote (lead rest : List Char) (noQuote : '"' ∉ lead) :
    (lead ++ '"' :: rest).takeWhile (· != '"') = lead := by
  induction lead with
  | nil => simp
  | cons c cs ih =>
      have different : c ≠ '"' := fun same => noQuote (by simp [same])
      have tailFree : '"' ∉ cs := fun member => noQuote (List.mem_cons_of_mem _ member)
      simp [different, ih tailFree]

/-- Both the data name and initialized bytes are uniquely determined by the
whole declaration text. This uses the independent lexical/literal relations,
not equality with the renderer as the definition of valid syntax. -/
theorem denotes_unique (first : Denotes reserved source name₁ object₁)
    (second : Denotes reserved source name₂ object₂) : name₁ = name₂ ∧ object₁ = object₂ := by
  obtain ⟨valid₁, lead₁, literal₁, suffix₁, source₁, head₁, string₁, tail₁⟩ := first
  obtain ⟨valid₂, lead₂, literal₂, suffix₂, source₂, head₂, string₂, tail₂⟩ := second
  obtain ⟨body₁, bytes₁, quoted₁, fragments₁, objectEq₁⟩ := string₁
  obtain ⟨body₂, bytes₂, quoted₂, fragments₂, objectEq₂⟩ := string₂
  have joined := source₁.symm.trans source₂
  have sameLead : lead₁ = lead₂ := by
    have taken := congrArg (List.takeWhile (· != '"')) joined
    simpa only [quoted₁, quoted₂, List.append_assoc, List.cons_append,
      before_quote _ _ (lex_no_quote head₁), before_quote _ _ (lex_no_quote head₂)] using taken
  have sameSuffix : suffix₁ = suffix₂ := by
    have reversed := congrArg (fun text : List Char => text.reverse.takeWhile (· != '"')) joined
    simp only [quoted₁, quoted₂, List.reverse_append, List.reverse_cons,
      List.append_assoc, List.cons_append, List.nil_append] at reversed
    have end₁ : '"' ∉ suffix₁.reverse := by simpa using lex_no_quote tail₁
    have end₂ : '"' ∉ suffix₂.reverse := by simpa using lex_no_quote tail₂
    rw [before_quote _ _ end₁, before_quote _ _ end₂] at reversed
    exact List.reverse_inj.mp reversed
  subst lead₂
  subst suffix₂
  have sameLiteral : literal₁ = literal₂ :=
    List.append_cancel_right (List.append_cancel_left (by simpa only [List.append_assoc] using joined))
  have scanned₁ := (Scanner.lex_correct config (String.ofList lead₁) _).mpr
    (by simpa only [String.toList_ofList] using head₁)
  have scanned₂ := (Scanner.lex_correct config (String.ofList lead₁) _).mpr
    (by simpa only [String.toList_ofList] using head₂)
  have sameTokens := Except.ok.inj (scanned₁.symm.trans scanned₂)
  refine ⟨?_, ?_⟩
  · simpa only [List.map_cons, List.map_nil, List.cons.injEq, Token.literal.injEq,
      and_true, true_and] using sameTokens
  · apply CString.denotes_unique
      ⟨body₁, bytes₁, quoted₁, fragments₁, objectEq₁⟩
    exact sameLiteral.symm ▸ ⟨body₂, bytes₂, quoted₂, fragments₂, objectEq₂⟩

private theorem identifier_char (c : Char) (valid : identRest c = true) :
    32 ≤ c.toNat ∧ c.toNat ≤ 126 ∧ c ≠ '?' := by
  simp only [identRest, identStart, asciiLetter, Char.isDigit, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at valid
  change (((97 ≤ c.toNat ∧ c.toNat ≤ 122) ∨ (65 ≤ c.toNat ∧ c.toNat ≤ 90)) ∨ c = '_') ∨
    (48 ≤ c.toNat ∧ c.toNat ≤ 57) at valid
  rcases valid with (((⟨lo, hi⟩ | ⟨lo, hi⟩) | rfl) | ⟨lo, hi⟩)
  all_goals first
  | decide +kernel
  | refine ⟨by omega, by omega, ?_⟩
    intro eq
    have ascii : c.toNat = 63 := congrArg Char.toNat eq
    omega

private theorem identifier_chars (valid : CIdentifier.valid reserved name = true) :
    ∀ c ∈ name.toList, 32 ≤ c.toNat ∧ c.toNat ≤ 126 ∧ c ≠ '?' := by
  obtain ⟨head, tail, same, start, rest⟩ := CIdentifier.word_parts reserved name valid
  intro c member
  rw [same] at member
  rcases List.mem_cons.mp member with rfl | member
  · exact identifier_char c (by simp [identRest, start])
  · exact identifier_char c (List.all_eq_true.mp rest c member)

private theorem question_free_safe (text : List Char) (noQuestion : ∀ c ∈ text, c ≠ '?')
    (previous : Bool) : CString.safeFrom previous text = true := by
  induction text generalizing previous with
  | nil => rfl
  | cons c rest ih =>
      have different := noQuestion c (by simp)
      simp [CString.safeFrom, different, ih (fun c member => noQuestion c (by simp [member]))]

theorem render_ascii (entry : Entry) (valid : CIdentifier.valid reserved entry.name = true) :
    CString.printableASCII (render entry).toList = true := by
  have nameASCII : CString.printableASCII entry.name.toList = true := by
    apply List.all_eq_true.mpr
    intro c member
    have ⟨lo, hi, _⟩ := identifier_chars valid c member
    simp [lo, hi]
  simp only [render, String.toList_append, CString.ascii_append, nameASCII, CString.quote_ascii]
  decide +kernel

theorem render_safe (entry : Entry) (valid : CIdentifier.valid reserved entry.name = true) :
    CString.safeFrom false (render entry).toList = true := by
  have nameSafe : ∀ previous, CString.safeFrom previous entry.name.toList = true :=
    question_free_safe _ (fun c member => (identifier_chars valid c member).2.2)
  simp only [render, String.toList_append, CString.safe_append, nameSafe, Bool.and_true]
  simp [CString.endMark, List.foldl_append, CString.safeFrom, CString.quote_safe]

theorem render_preprocessed (entry : Entry) (valid : CIdentifier.valid reserved entry.name = true)
    (steps : Relation.ReflTransGen CString.Rewrite (render entry).toList processed) :
    processed = (render entry).toList := by
  induction steps with
  | refl => rfl
  | tail path step ih =>
      rw [ih] at step
      exact False.elim (CString.no_rewrite _ _ (render_safe entry valid) (render_ascii entry valid) step)

private theorem prefix_lex (name : String) (valid : CIdentifier.valid reserved name = true) :
    Scanner.Lexes config ("static const char " ++ name ++ "[] = ").toList
      (["static", "const", "char", name, "[", "]", "="].map Token.literal) := by
  simp only [String.toList_append, List.map_cons, List.map_nil]
  c_lex_fixed
  apply CIdentifier.lex_word config rfl rfl rfl rfl name '[' _ _
    (CIdentifier.word_parts reserved name valid) (by decide +kernel)
  c_lex_fixed

theorem render_denotes (entry : Entry) (valid : CIdentifier.valid reserved entry.name = true) :
    Denotes reserved (render entry).toList entry.name (bytes entry.text) := by
  refine ⟨valid, ("static const char " ++ entry.name ++ "[] = ").toList,
    (CTree.quote entry.text).toList, [';'], ?_, prefix_lex entry.name valid,
    CString.quote_correct entry.text, ?_⟩
  · simp [render, String.toList_append, List.append_assoc]
  · c_lex_fixed

/-- Exact declaration name and initializer bytes after every modeled
preprocessing sequence. This is a syntax contract, with native storage and
surrounding translation-unit legality still outside its scope. -/
def Correct (reserved : List String) (entry : Entry) (source : List Char) : Prop :=
  CString.printableASCII source = true ∧
  ∀ processed, Relation.ReflTransGen CString.Rewrite source processed →
    ∀ name object, Denotes reserved processed name object ↔
      name = entry.name ∧ object = bytes entry.text

theorem render_correct (entry : Entry) (valid : CIdentifier.valid reserved entry.name = true) :
    Correct reserved entry (render entry).toList := by
  refine ⟨render_ascii entry valid, ?_⟩
  intro processed steps name object
  rw [render_preprocessed entry valid steps]
  constructor
  · intro interpreted
    exact denotes_unique interpreted (render_denotes entry valid)
  · rintro ⟨rfl, rfl⟩
    exact render_denotes entry valid

/-- The independently interpreted initializer bytes are present in the
constructed symbolic array, for either selected signed-char interpretation. -/
theorem render_storage (pool : Pool reserved) (member : entry ∈ pool.entries)
    (before : Heap) (firstBlock : Nat) (signed : Bool) :
    Denotes ("isfinite" :: reserved) (render entry).toList entry.name (bytes entry.text) ∧
    ∀ index byte, (bytes entry.text)[index]? = some byte →
      readByte (pool.install before firstBlock signed) ((entry.address firstBlock).index index) = some byte :=
  ⟨render_denotes (reserved := "isfinite" :: reserved) entry (pool.entry_valid member).1,
    fun _ _ atByte => (pool.installed before firstBlock signed member).read_byte atByte⟩

end Rumoca.CLiteral.Declaration
