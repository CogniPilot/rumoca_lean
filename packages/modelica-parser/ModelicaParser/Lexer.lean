import Parser.Token

open Parser

namespace Rumoca

def modelicaSpace := Parser.asciiSpace

/-- MLS 3.7 §2.3.3, plus the four predefined type names that cannot be redeclared. -/
def reserved : List String :=
  ["algorithm", "and", "annotation", "block", "break", "class", "connect",
   "connector", "constant", "constrainedby", "der", "discrete", "each", "else",
   "elseif", "elsewhen", "encapsulated", "end", "enumeration", "equation",
   "expandable", "extends", "external", "false", "final", "flow", "for",
   "function", "if", "import", "impure", "in", "initial", "inner", "input",
   "loop", "model", "not", "operator", "or", "outer", "output", "package",
   "parameter", "partial", "protected", "public", "pure", "record", "redeclare",
   "replaceable", "return", "stream", "then", "time", "true", "type", "when",
   "while", "within", "Real", "Integer", "Boolean", "String"]

def classifyWord (s : String) : Token :=
  if reserved.contains s then .literal s else .ident s

def punctuation (c : Char) : Bool := [';', '(', ')', '=', ',', '[', ']'].contains c

/-- Characters of a signed decimal literal: digits, the fraction point, the
exponent letter and a sign. A leading digit or sign begins a number. -/
def numberChar (c : Char) : Bool :=
  c.isDigit || c == '.' || c == 'e' || c == 'E' || c == '+' || c == '-'

def numberStart (c : Char) : Bool := c.isDigit || c == '+' || c == '-'

/-- A pure digit run keeps the exact literal-terminal spelling the admitted
profiles match (`'0'`, `'1'`, `'2'`); a spelling that carries a sign, point or
exponent becomes a value-erasing number token that resolution parses. Every
existing source uses only single-digit literals, whose class is unchanged. -/
def numberToken (cs : List Char) : Token :=
  if cs.all Char.isDigit then .literal (String.ofList cs) else .number (String.ofList cs)

theorem numberToken_text (cs : List Char) : (numberToken cs).text = String.ofList cs := by
  unfold numberToken; split <;> rfl

/-- Declarative maximal-munch lexical rules for the admitted ASCII slice.
The first character chooses the token class; takeWhile/dropWhile specify the
maximal remaining word. Comments and quoted identifiers are outside this core. -/
inductive Lexes : List Char → List Token → Prop where
  | nil : Lexes [] []
  | space : modelicaSpace c = true → Lexes cs ts → Lexes (c :: cs) ts
  | ident : modelicaSpace c = false → identStart c = true →
      Lexes (cs.dropWhile identRest) ts →
      Lexes (c :: cs) (classifyWord (String.ofList (c :: cs.takeWhile identRest)) :: ts)
  | number : modelicaSpace c = false → identStart c = false → numberStart c = true →
      Lexes (cs.dropWhile numberChar) ts →
      Lexes (c :: cs) (numberToken (c :: cs.takeWhile numberChar) :: ts)
  | punct : modelicaSpace c = false → identStart c = false → numberStart c = false →
      punctuation c = true → Lexes cs ts →
      Lexes (c :: cs) (.literal (String.singleton c) :: ts)
  | dotmul : Lexes cs ts → Lexes ('.' :: '*' :: cs) (.literal ".*" :: ts)

private def prepend (t : Token) : Except Diagnostic (List Token) → Except Diagnostic (List Token)
  | .error e => .error e
  | .ok ts => .ok (t :: ts)

private theorem prepend_ok (t : Token) (r : Except Diagnostic (List Token)) (ts : List Token)
    (h : prepend t r = .ok ts) : ∃ tail, r = .ok tail ∧ ts = t :: tail := by
  cases r with
  | error e => contradiction
  | ok tail => exact ⟨tail, rfl, (Except.ok.inj h).symm⟩

/-- Fuel bounds recursive calls by source length; there is no parser search. -/
def scan (total : Nat) : Nat → List Char → Except Diagnostic (List Token)
  | 0, _ => .error ⟨"lex", 0, "input limit exceeded"⟩
  | _ + 1, [] => .ok []
  | fuel + 1, c :: rest =>
    if modelicaSpace c then scan total fuel rest
    else if identStart c then
      prepend (classifyWord (String.ofList (c :: rest.takeWhile identRest)))
        (scan total fuel (rest.dropWhile identRest))
    else if numberStart c then
      prepend (numberToken (c :: rest.takeWhile numberChar))
        (scan total fuel (rest.dropWhile numberChar))
    else if punctuation c then
      prepend (.literal (String.singleton c)) (scan total fuel rest)
    else if c = '.' ∧ rest.head? = some '*' then
      prepend (.literal ".*") (scan total fuel (rest.drop 1))
    else
      .error ⟨"lex", total - (rest.length + 1), s!"unsupported character {repr c}"⟩

theorem scan_sound (total fuel : Nat) (cs : List Char) (ts : List Token)
    (h : scan total fuel cs = .ok ts) : Lexes cs ts := by
  induction fuel generalizing cs ts with
  | zero => simp [scan] at h
  | succ fuel ih =>
    cases cs with
    | nil => cases Except.ok.inj h; exact .nil
    | cons c cs =>
      simp only [scan] at h
      split at h
      · exact .space (by assumption) (ih _ _ h)
      · rename_i hs
        have hs' : modelicaSpace c = false := Bool.eq_false_iff.mpr hs
        split at h
        · obtain ⟨tail, ht, rfl⟩ := prepend_ok _ _ _ h
          exact .ident hs' (by assumption) (ih _ _ ht)
        · rename_i hi
          have hi' : identStart c = false := Bool.eq_false_iff.mpr hi
          split at h
          · obtain ⟨tail, ht, rfl⟩ := prepend_ok _ _ _ h
            exact .number hs' hi' (by assumption) (ih _ _ ht)
          · rename_i hd
            have hns : numberStart c = false := Bool.eq_false_iff.mpr hd
            split at h
            · obtain ⟨tail, ht, rfl⟩ := prepend_ok _ _ _ h
              exact .punct hs' hi' hns (by assumption) (ih _ _ ht)
            · split at h
              · rename_i hop
                obtain ⟨hc, hhead⟩ := hop
                subst c
                cases cs with
                | nil => simp at hhead
                | cons first rest =>
                  have hf : first = '*' := Option.some.inj hhead
                  subst first
                  obtain ⟨tail, ht, rfl⟩ := prepend_ok _ _ _ h
                  exact .dotmul (ih _ _ ht)
              · contradiction

theorem scan_complete (h : Lexes cs ts) (total fuel : Nat) (bound : cs.length < fuel) :
    scan total fuel cs = .ok ts := by
  induction h generalizing fuel with
  | nil => cases fuel <;> simp_all [scan]
  | space hs h ih =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [scan, hs, ih fuel (by simpa using bound)]
  | @ident c ts cs hs hi h ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hd := congrArg List.length (List.takeWhile_append_dropWhile (p := identRest) (l := cs))
      simp only [List.length_append] at hd
      simp [scan, hs, hi, ih fuel (by simp only [List.length_cons] at bound; omega), prepend]
  | @number c ts cs hs hi hd h ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hl := congrArg List.length (List.takeWhile_append_dropWhile (p := numberChar) (l := cs))
      simp only [List.length_append] at hl
      simp [scan, hs, hi, hd, ih fuel (by simp only [List.length_cons] at bound; omega), prepend]
  | punct hs hi hd hp h ih =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [scan, hs, hi, hd, hp, ih fuel (by simpa using bound), prepend]
  | dotmul h ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hs : modelicaSpace '.' = false := by decide
      have hi : identStart '.' = false := by decide
      have hn : numberStart '.' = false := by decide
      have hp : punctuation '.' = false := by decide
      simp [scan, hs, hi, hn, hp,
        ih fuel (by simp only [List.length_cons] at bound; omega), prepend]

def lex (source : String) : Except Diagnostic (List Token) :=
  let cs := source.toList
  scan cs.length (cs.length + 1) cs

theorem lex_correct (source : String) (ts : List Token) :
    lex source = .ok ts ↔ Lexes source.toList ts :=
  ⟨scan_sound _ _ _ _, fun h => scan_complete h _ _ (Nat.lt_succ_self _)⟩

end Rumoca
