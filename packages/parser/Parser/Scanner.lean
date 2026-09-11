import Parser.Token

/-! Reusable scanner for the two tiny grammar profiles. Configurations define
word classification and punctuation; this does not implement either language's
full lexical specification (comments and quoted names remain unsupported). -/
namespace Parser.Scanner

structure Config where
  space : Char → Bool := asciiSpace
  wordStart : Char → Bool
  wordRest : Char → Bool
  numberRest : Char → Bool
  classify : String → Token
  single : Char → Bool
  pair : Char → Option Char

/-- Prefer a configured two-character symbol when its second character is
present; otherwise a configured single-character symbol remains available. -/
def pairMatches (cfg : Config) (c : Char) (rest : List Char) : Bool :=
  match cfg.pair c with
  | none => false
  | some d => match rest with
    | [] => false
    | e :: _ => e == d

inductive SymbolLexes (cfg : Config) : List Char → Token → List Char → Prop where
  | single : pairMatches cfg c cs = false → cfg.single c = true →
      SymbolLexes cfg (c :: cs) (.literal (String.singleton c)) cs
  | pair : cfg.pair c = some d →
      SymbolLexes cfg (c :: d :: cs) (.literal (String.ofList [c, d])) cs

theorem SymbolLexes.single_unpaired (noPair : cfg.pair c = none) (single : cfg.single c = true) :
    SymbolLexes cfg (c :: cs) (.literal (String.singleton c)) cs :=
  .single (by simp [pairMatches, noPair]) single

def readSymbol (cfg : Config) : List Char → Option (Token × List Char)
  | [] => none
  | c :: cs =>
    if pairMatches cfg c cs then
      match cs with
      | [] => none
      | d :: rest => some (.literal (String.ofList [c, d]), rest)
    else if cfg.single c then some (.literal (String.singleton c), cs) else none

theorem pairMatches_iff : pairMatches cfg c cs = true ↔
    ∃ d rest, cs = d :: rest ∧ cfg.pair c = some d := by
  cases found : cfg.pair c with
  | none => simp [pairMatches, found]
  | some d =>
      cases cs with
      | nil => simp [pairMatches, found]
      | cons e es =>
          constructor
          · intro matched
            have same : e = d := by simpa only [pairMatches, found, beq_iff_eq] using matched
            subst e
            exact ⟨d, es, rfl, rfl⟩
          · rintro ⟨e', rest, same, configured⟩
            cases same
            have equal := Option.some.inj configured
            subst d
            simp [pairMatches, found]

theorem symbol_correct : readSymbol cfg cs = some (t, rest) ↔ SymbolLexes cfg cs t rest := by
  constructor
  · intro h
    cases cs with
    | nil => simp [readSymbol] at h
    | cons c cs =>
      cases matched : pairMatches cfg c cs with
      | false =>
        simp only [readSymbol, matched, Bool.false_eq_true, ↓reduceIte] at h
        split at h
        · cases Option.some.inj h; exact .single matched (by assumption)
        · contradiction
      | true =>
        obtain ⟨d, rest, rfl, configured⟩ := pairMatches_iff.mp matched
        simp only [readSymbol, matched, ↓reduceIte] at h
        cases Option.some.inj h
        exact .pair configured
  · intro h
    cases h with
    | single hp hs => simp [readSymbol, hp, hs]
    | pair hp => simp [readSymbol, pairMatches, hp]

/-- Configurations whose single and pair prefixes are disjoint retain the
previous strict-pair behavior, including rejection of a missing second byte. -/
theorem readSymbol_disjoint (cfg : Config)
    (disjoint : ∀ c, cfg.single c = true → cfg.pair c = none) (text : List Char) :
    readSymbol cfg text = (match text with
      | [] => none
      | c :: cs => match cfg.pair c with
        | none => if cfg.single c then some (.literal (String.singleton c), cs) else none
        | some d => match cs with
          | [] => none
          | e :: es => if e = d then some (.literal (String.ofList [c, d]), es) else none) := by
  cases text with
  | nil => rfl
  | cons c cs =>
      cases found : cfg.pair c with
      | none => simp [readSymbol, pairMatches, found]
      | some d =>
          have unavailable : cfg.single c = false := by
            apply Bool.eq_false_iff.mpr
            intro single
            rw [disjoint c single] at found
            contradiction
          cases cs with
          | nil => simp [readSymbol, pairMatches, found, unavailable]
          | cons e es =>
              by_cases same : e = d
              · subst e; simp [readSymbol, pairMatches, found]
              · simp [readSymbol, pairMatches, found, unavailable, same]

theorem symbol_shorter (h : SymbolLexes cfg cs t rest) : rest.length < cs.length := by
  cases h <;> simp only [List.length_cons] <;> omega

inductive Lexes (cfg : Config) : List Char → List Token → Prop where
  | nil : Lexes cfg [] []
  | space : cfg.space c = true → Lexes cfg cs ts → Lexes cfg (c :: cs) ts
  | word : cfg.space c = false → cfg.wordStart c = true →
      Lexes cfg (cs.dropWhile cfg.wordRest) ts →
      Lexes cfg (c :: cs) (cfg.classify (String.ofList (c :: cs.takeWhile cfg.wordRest)) :: ts)
  | number : cfg.space c = false → cfg.wordStart c = false → c.isDigit = true →
      Lexes cfg (cs.dropWhile cfg.numberRest) ts →
      Lexes cfg (c :: cs) (.literal (String.ofList (c :: cs.takeWhile cfg.numberRest)) :: ts)
  | symbol : cfg.space c = false → cfg.wordStart c = false → c.isDigit = false →
      SymbolLexes cfg (c :: cs) t rest → Lexes cfg rest ts → Lexes cfg (c :: cs) (t :: ts)

def scan (cfg : Config) (total : Nat) : Nat → List Char → Except Diagnostic (List Token)
  | 0, _ => .error ⟨"lex", 0, "input limit exceeded"⟩
  | _ + 1, [] => .ok []
  | fuel + 1, c :: rest =>
    if cfg.space c then scan cfg total fuel rest
    else if cfg.wordStart c then
      (cfg.classify (String.ofList (c :: rest.takeWhile cfg.wordRest)) :: ·) <$>
        scan cfg total fuel (rest.dropWhile cfg.wordRest)
    else if c.isDigit then
      (.literal (String.ofList (c :: rest.takeWhile cfg.numberRest)) :: ·) <$>
        scan cfg total fuel (rest.dropWhile cfg.numberRest)
    else match readSymbol cfg (c :: rest) with
      | some (token, tail) => (token :: ·) <$> scan cfg total fuel tail
      | none => .error ⟨"lex", total - (rest.length + 1), "unsupported character or punctuation"⟩

private theorem cons_ok (token : Token) (r : Except Diagnostic (List Token))
    (h : (token :: ·) <$> r = .ok ts) : ∃ tail, r = .ok tail ∧ ts = token :: tail := by
  cases r with
  | error => contradiction
  | ok tail => exact ⟨tail, rfl, (Except.ok.inj h).symm⟩

theorem scan_sound (h : scan cfg total fuel cs = .ok ts) : Lexes cfg cs ts := by
  induction fuel generalizing cs ts with
  | zero => contradiction
  | succ fuel ih =>
    cases cs with
    | nil => cases Except.ok.inj h; exact .nil
    | cons c cs =>
      simp only [scan] at h
      split at h
      · exact .space (by assumption) (ih h)
      · rename_i hs
        have hs' := Bool.eq_false_iff.mpr hs
        split at h
        · obtain ⟨tail, ht, rfl⟩ := cons_ok _ _ h
          exact .word hs' (by assumption) (ih ht)
        · rename_i hw
          have hw' := Bool.eq_false_iff.mpr hw
          split at h
          · obtain ⟨tail, ht, rfl⟩ := cons_ok _ _ h
            exact .number hs' hw' (by assumption) (ih ht)
          · rename_i hd
            cases hr : readSymbol cfg (c :: cs) with
            | none => simp [hr] at h
            | some pair =>
              rcases pair with ⟨t, rest⟩
              rw [hr] at h
              obtain ⟨tail, ht, rfl⟩ := cons_ok _ _ h
              exact .symbol hs' hw' (Bool.eq_false_iff.mpr hd)
                (symbol_correct.mp hr) (ih ht)

theorem scan_complete (h : Lexes cfg cs ts) (total fuel : Nat) (bound : cs.length < fuel) :
    scan cfg total fuel cs = .ok ts := by
  induction h generalizing fuel with
  | nil => cases fuel <;> simp_all [scan]
  | space hs h ih =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [scan, hs, ih fuel (by simpa using bound)]
  | @word c ts cs hs hw h ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hd := congrArg List.length (List.takeWhile_append_dropWhile (p := cfg.wordRest) (l := cs))
      simp only [List.length_append] at hd
      simp [scan, hs, hw, ih fuel (by simp only [List.length_cons] at bound; omega)]
      rfl
  | @number c ts cs hs hw hd h ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hl := congrArg List.length (List.takeWhile_append_dropWhile (p := cfg.numberRest) (l := cs))
      simp only [List.length_append] at hl
      simp [scan, hs, hw, hd, ih fuel (by simp only [List.length_cons] at bound; omega)]
      rfl
  | symbol hs hw hd sym h ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hl := symbol_shorter sym
      simp [scan, hs, hw, hd, symbol_correct.mpr sym, ih fuel (by omega)]
      rfl

def lex (cfg : Config) (source : String) : Except Diagnostic (List Token) :=
  scan cfg source.toList.length (source.toList.length + 1) source.toList

theorem lex_correct (cfg : Config) (source : String) (ts : List Token) :
    lex cfg source = .ok ts ↔ Lexes cfg source.toList ts :=
  ⟨scan_sound, fun h => scan_complete h _ _ (Nat.lt_succ_self _)⟩

end Parser.Scanner
