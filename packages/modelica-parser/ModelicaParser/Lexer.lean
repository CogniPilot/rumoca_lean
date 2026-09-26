import Parser.Token

open Parser

namespace Rumoca

def modelicaSpace := Parser.asciiSpace

/-- MLS 3.7 §2.3.3 keywords. Predefined type names such as `Real` are ordinary
identifiers (§2.3.3 does not reserve them); static semantics rejects them as
declared or referenced names. -/
def reserved : List String :=
  ["algorithm", "and", "annotation", "block", "break", "class", "connect",
   "connector", "constant", "constrainedby", "der", "discrete", "each", "else",
   "elseif", "elsewhen", "encapsulated", "end", "enumeration", "equation",
   "expandable", "extends", "external", "false", "final", "flow", "for",
   "function", "if", "import", "impure", "in", "initial", "inner", "input",
   "loop", "model", "not", "operator", "or", "outer", "output", "package",
   "parameter", "partial", "protected", "public", "pure", "record", "redeclare",
   "replaceable", "return", "stream", "then", "time", "true", "type", "when",
   "while", "within"]

def classifyWord (s : String) : Token :=
  if reserved.contains s then .literal s else .ident s

/-- Single-character symbols. `.` separates name components; the pair `.*`, a
number and a comment are recognized before it. -/
def punctuation (c : Char) : Bool :=
  [';', '(', ')', '=', ',', '[', ']', '{', '}', '*', '/', '.', '+', '-'].contains c

/-- The length of the leading digit run. -/
def digitRun (cs : List Char) : Nat := (cs.takeWhile Char.isDigit).length

/-- The length of an exponentLength `(e|E) [+|-] DIGIT {DIGIT}` at the head, or 0. -/
def exponentLength : List Char → Nat
  | e :: s :: more =>
    if e = 'e' ∨ e = 'E' then
      if s.isDigit then 1 + digitRun (s :: more)
      else if (s = '+' ∨ s = '-') ∧ 0 < digitRun more then 2 + digitRun more
      else 0
    else 0
  | _ => 0

/-- The length of a fractionLength `. {DIGIT}` at the head, or 0. -/
def fractionLength : List Char → Nat
  | '.' :: rest => 1 + digitRun rest
  | _ => 0

/-- MLS A.1 UNSIGNED-INTEGER and UNSIGNED-REAL by maximal munch: the length of
the number at the head of the characters. A sign is never part of a number. -/
def numberLength (cs : List Char) : Nat :=
  let whole := digitRun cs
  let point := fractionLength (cs.drop whole)
  whole + point + exponentLength (cs.drop (whole + point))

/-- A number begins with a digit, or with `.` followed by a digit. -/
def numberStart (c : Char) (cs : List Char) : Bool :=
  c.isDigit || (c == '.' && (cs.head?.map Char.isDigit).getD false)

theorem numberLength_pos (c : Char) (cs : List Char) (start : numberStart c cs = true) :
    0 < numberLength (c :: cs) := by
  have le : digitRun (c :: cs) + fractionLength ((c :: cs).drop (digitRun (c :: cs))) ≤
      numberLength (c :: cs) := by
    simp only [numberLength]; omega
  by_cases d : c.isDigit
  · have : digitRun (c :: cs) = digitRun cs + 1 := by simp [digitRun, d]
    omega
  · have point : c = '.' := by simp [numberStart, d] at start; exact start.1
    have zero : digitRun (c :: cs) = 0 := by simp [digitRun, d]
    rw [zero] at le
    subst point
    simp [fractionLength] at le
    omega

/-- MLS A.1 S-ESCAPE characters after a backslash. -/
def escapeChar (c : Char) : Bool := ['\'', '"', '?', '\\', 'a', 'b', 'f', 'n', 'r', 't', 'v'].contains c

/-- The length of a STRING body through its closing quote: any character except
`"` and `\` (line ends included), or an S-ESCAPE. `none` for an unterminated
string or an invalid escape. The first unescaped quote closes the string. -/
def stringLength : List Char → Option Nat
  | [] => none
  | '"' :: _ => some 1
  | '\\' :: e :: rest => if escapeChar e then (stringLength rest).map (· + 2) else none
  | '\\' :: [] => none
  | _ :: rest => (stringLength rest).map (· + 1)

/-- The length of a block comment body through the first `*/`; comments do not
nest. `none` for an unterminated comment. -/
def blockCommentLength : List Char → Option Nat
  | [] => none
  | '*' :: '/' :: _ => some 2
  | _ :: rest => (blockCommentLength rest).map (· + 1)

/-- The length of a line comment body up to, not including, the line end. -/
def lineCommentLength (cs : List Char) : Nat := (cs.takeWhile (· != '\n')).length

/-- The pair `.*` begins the characters. -/
def pointwiseStart (c : Char) (cs : List Char) : Bool := c == '.' && cs.head? == some '*'

/-- `//` or `/*` begins a comment. -/
def commentStart (c : Char) (cs : List Char) : Bool :=
  c == '/' && (cs.head? == some '/' || cs.head? == some '*')

/-- Declarative maximal-munch lexical rules (MLS 3.7 A.1) for the ASCII slice.
The first characters choose the lexical unit; each unit takes the longest
spelling of its class. Comments are lexical units of their own class, so their
positions are retained; they are not grammar terminals. Quoted identifiers are
not scanned. -/
inductive Lexes : List Char → List Token → Prop where
  | nil : Lexes [] []
  | space : modelicaSpace c = true → Lexes cs ts → Lexes (c :: cs) ts
  | ident : modelicaSpace c = false → identStart c = true →
      Lexes (cs.dropWhile identRest) ts →
      Lexes (c :: cs) (classifyWord (String.ofList (c :: cs.takeWhile identRest)) :: ts)
  | number : modelicaSpace c = false → identStart c = false → numberStart c cs = true →
      Lexes ((c :: cs).drop (numberLength (c :: cs))) ts →
      Lexes (c :: cs) (.number (String.ofList ((c :: cs).take (numberLength (c :: cs)))) :: ts)
  | string : stringLength cs = some n → Lexes (cs.drop n) ts →
      Lexes ('"' :: cs) (.string (String.ofList ('"' :: cs.take n)) :: ts)
  | lineComment : Lexes (cs.drop (lineCommentLength cs)) ts →
      Lexes ('/' :: '/' :: cs) (.comment (String.ofList ('/' :: '/' :: cs.take (lineCommentLength cs))) :: ts)
  | blockComment : blockCommentLength cs = some n → Lexes (cs.drop n) ts →
      Lexes ('/' :: '*' :: cs) (.comment (String.ofList ('/' :: '*' :: cs.take n)) :: ts)
  | dotmul : Lexes cs ts → Lexes ('.' :: '*' :: cs) (.literal ".*" :: ts)
  | punct : modelicaSpace c = false → identStart c = false → numberStart c cs = false →
      commentStart c cs = false → pointwiseStart c cs = false → punctuation c = true → Lexes cs ts →
      Lexes (c :: cs) (.literal (String.singleton c) :: ts)

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
    else if numberStart c rest then
      prepend (.number (String.ofList ((c :: rest).take (numberLength (c :: rest)))))
        (scan total fuel ((c :: rest).drop (numberLength (c :: rest))))
    else if c = '"' then
      match stringLength rest with
      | some n => prepend (.string (String.ofList ('"' :: rest.take n))) (scan total fuel (rest.drop n))
      | none => .error ⟨"lex", total - (rest.length + 1), "unterminated string or invalid escape"⟩
    else if commentStart c rest then
      match rest with
      | '/' :: body =>
        prepend (.comment (String.ofList ('/' :: '/' :: body.take (lineCommentLength body))))
          (scan total fuel (body.drop (lineCommentLength body)))
      | '*' :: body =>
        match blockCommentLength body with
        | some n => prepend (.comment (String.ofList ('/' :: '*' :: body.take n)))
            (scan total fuel (body.drop n))
        | none => .error ⟨"lex", total - (rest.length + 1), "unterminated comment"⟩
      | _ => .error ⟨"lex", total - (rest.length + 1), "unsupported character"⟩
    else if pointwiseStart c rest then
      prepend (.literal ".*") (scan total fuel (rest.drop 1))
    else if punctuation c then
      prepend (.literal (String.singleton c)) (scan total fuel rest)
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
          · rename_i hn
            have hn' : numberStart c cs = false := Bool.eq_false_iff.mpr hn
            split at h
            · rename_i quote
              subst quote
              split at h
              · rename_i n found
                obtain ⟨tail, ht, rfl⟩ := prepend_ok _ _ _ h
                exact .string found (ih _ _ ht)
              · contradiction
            · rename_i unquoted
              split at h
              · rename_i opens
                simp only [commentStart, Bool.and_eq_true, beq_iff_eq] at opens
                obtain ⟨rfl, _⟩ := opens
                split at h
                · obtain ⟨tail, ht, rfl⟩ := prepend_ok _ _ _ h
                  exact .lineComment (ih _ _ ht)
                · split at h
                  · rename_i n found
                    obtain ⟨tail, ht, rfl⟩ := prepend_ok _ _ _ h
                    exact .blockComment found (ih _ _ ht)
                  · contradiction
                · contradiction
              · rename_i uncommented
                have hc : commentStart c cs = false := Bool.eq_false_iff.mpr uncommented
                split at h
                · rename_i pair
                  simp only [pointwiseStart, Bool.and_eq_true, beq_iff_eq] at pair
                  obtain ⟨rfl, head⟩ := pair
                  cases cs with
                  | nil => simp at head
                  | cons first rest =>
                    cases Option.some.inj head
                    obtain ⟨tail, ht, rfl⟩ := prepend_ok _ _ _ h
                    exact .dotmul (ih _ _ ht)
                · rename_i single
                  have hp : pointwiseStart c cs = false := Bool.eq_false_iff.mpr single
                  split at h
                  · obtain ⟨tail, ht, rfl⟩ := prepend_ok _ _ _ h
                    exact .punct hs' hi' hn' hc hp (by assumption) (ih _ _ ht)
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
  | @number c cs ts hs hi hn h ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have positive := numberLength_pos c cs hn
      have shorter : ((c :: cs).drop (numberLength (c :: cs))).length < fuel := by
        simp only [List.length_drop, List.length_cons] at bound ⊢; omega
      simp [scan, hs, hi, hn, ih fuel shorter, prepend]
  | string found _ ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp [scan, modelicaSpace, Parser.asciiSpace, identStart, asciiLetter, numberStart, found,
        ih fuel (by simp only [List.length_drop, List.length_cons] at bound ⊢; omega), prepend]
  | lineComment _ ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp [scan, modelicaSpace, Parser.asciiSpace, identStart, asciiLetter, numberStart,
        commentStart, ih fuel (by simp only [List.length_drop, List.length_cons] at bound ⊢; omega),
        prepend]
  | blockComment found _ ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp [scan, modelicaSpace, Parser.asciiSpace, identStart, asciiLetter, numberStart,
        commentStart, found,
        ih fuel (by simp only [List.length_drop, List.length_cons] at bound ⊢; omega), prepend]
  | dotmul _ ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp [scan, modelicaSpace, Parser.asciiSpace, identStart, asciiLetter, numberStart,
        commentStart, pointwiseStart, ih fuel (by simp only [List.length_cons] at bound; omega), prepend]
  | @punct c cs ts hs hi hn hc hp hq h ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have quote : c ≠ '"' := by
        intro same; subst same; simp [punctuation] at hq
      simp [scan, hs, hi, hn, hc, hp, hq, quote, ih fuel (by simpa using bound), prepend]

def lex (source : String) : Except Diagnostic (List Token) :=
  let cs := source.toList
  scan cs.length (cs.length + 1) cs

theorem lex_correct (source : String) (ts : List Token) :
    lex source = .ok ts ↔ Lexes source.toList ts :=
  ⟨scan_sound _ _ _ _, fun h => scan_complete h _ _ (Nat.lt_succ_self _)⟩

/-- A lexed identifier token is not a reserved word and consists of identifier
characters only. -/
theorem Lexes.ident_word (lexed : Lexes cs ts) :
    ∀ name, .ident name ∈ ts → name ∉ reserved ∧ ∀ c ∈ name.toList, identRest c = true := by
  induction lexed with
  | nil => intro name member; cases member
  | space _ _ ih => exact ih
  | ident _ start _ ih =>
    intro name member
    rcases List.mem_cons.mp member with same | member
    · unfold classifyWord at same
      split at same
      · cases same
      · rename_i unreserved
        cases same
        refine ⟨fun r => unreserved (List.contains_iff_mem.mpr r), ?_⟩
        intro ch mem
        rw [String.toList_ofList] at mem
        rcases List.mem_cons.mp mem with rfl | mem
        · simp [identRest, start]
        · exact List.all_eq_true.mp List.all_takeWhile ch mem
    · exact ih name member
  | number _ _ _ _ ih | string _ _ ih | lineComment _ ih | blockComment _ _ ih | dotmul _ ih
    | punct _ _ _ _ _ _ _ ih =>
    intro name member
    rcases List.mem_cons.mp member with same | member
    · cases same
    · exact ih name member

/-- No lexed identifier is the reserved word `time` or contains a parenthesis. -/
theorem Lexes.ident_not_time (lexed : Lexes cs ts) (name : String) (member : .ident name ∈ ts) :
    name ≠ "time" ∧ '(' ∉ name.toList := by
  obtain ⟨unreserved, chars⟩ := lexed.ident_word name member
  refine ⟨fun same => unreserved (by rw [same]; decide), fun paren => ?_⟩
  have := chars '(' paren
  simp [identRest, identStart, asciiLetter] at this


/-- The characters of a STRING body: any character other than `"` and `\`, or a
backslash and an S-ESCAPE character. -/
inductive StringBody : List Char → Prop where
  | nil : StringBody []
  | char : c ≠ '"' → c ≠ '\\' → StringBody cs → StringBody (c :: cs)
  | escape : escapeChar e = true → StringBody cs → StringBody ('\\' :: e :: cs)

theorem stringLength_body {body rest : List Char} (valid : StringBody body) :
    stringLength (body ++ '"' :: rest) = some (body.length + 1) := by
  induction valid with
  | nil => simp [stringLength]
  | char quote backslash _ ih =>
    rw [List.cons_append, stringLength.eq_def]
    split <;> simp_all
  | escape escaped _ ih =>
    simp [stringLength, escaped, ih]

theorem stringLength_sound {cs : List Char} {n : Nat} (found : stringLength cs = some n) :
    ∃ body rest, cs = body ++ '"' :: rest ∧ StringBody body ∧ n = body.length + 1 := by
  induction cs using stringLength.induct generalizing n with
  | case1 => simp [stringLength] at found
  | case2 rest =>
    simp only [stringLength, Option.some.injEq] at found
    exact ⟨[], rest, rfl, .nil, found.symm⟩
  | case3 e rest escaped ih =>
    simp only [stringLength, escaped, ↓reduceIte, Option.map_eq_some_iff] at found
    obtain ⟨k, found, rfl⟩ := found
    obtain ⟨body, rest', rfl, valid, rfl⟩ := ih found
    exact ⟨'\\' :: e :: body, rest', rfl, .escape escaped valid, by simp⟩
  | case4 e rest unescaped => simp [stringLength, unescaped] at found
  | case5 => simp [stringLength] at found
  | case6 c rest quote backslash backslashEnd ih =>
    simp only [stringLength, Option.map_eq_some_iff] at found
    obtain ⟨k, found, rfl⟩ := found
    obtain ⟨body, rest', rfl, valid, rfl⟩ := ih found
    have plain : c ≠ '\\' := by
      intro same
      cases body with
      | nil => exact backslash '"' rest' same rfl
      | cons e more => exact backslash e (more ++ '"' :: rest') same rfl
    exact ⟨c :: body, rest', rfl, .char quote plain valid, by simp⟩

/-- A STRING ends at its first unescaped quote: the lexer takes exactly a
string body and that quote. -/
theorem string_maximal {cs : List Char} {n : Nat} :
    stringLength cs = some n ↔ ∃ body rest, cs = body ++ '"' :: rest ∧ StringBody body ∧
      n = body.length + 1 :=
  ⟨stringLength_sound, fun ⟨_, _, same, valid, length⟩ => by
    rw [same, length]; exact stringLength_body valid⟩

/-! ### STRING values -/

/-- The character an MLS 3.7 A.1 S-ESCAPE denotes: the quote, question-mark and
backslash escapes denote themselves; `\a` alert, `\b` backspace, `\f` form feed,
`\n` new line, `\r` carriage return, `\t` horizontal tab and `\v` vertical tab
denote their ASCII control characters. `none` for a character that is not an
S-ESCAPE. -/
def escapeValue : Char → Option Char
  | '\'' => some '\''
  | '"' => some '"'
  | '?' => some '?'
  | '\\' => some '\\'
  | 'a' => some (Char.ofNat 7)
  | 'b' => some (Char.ofNat 8)
  | 'f' => some (Char.ofNat 12)
  | 'n' => some '\n'
  | 'r' => some '\r'
  | 't' => some '\t'
  | 'v' => some (Char.ofNat 11)
  | _ => none

/-- Exactly the S-ESCAPE characters have a value. -/
theorem escapeValue_isSome (e : Char) : (escapeValue e).isSome = escapeChar e := by
  unfold escapeValue
  split <;> simp_all [escapeChar]

/-- The value of a STRING body: a character other than `"` and `\` denotes itself
and an S-ESCAPE denotes its character. -/
inductive Decodes : List Char → List Char → Prop where
  | nil : Decodes [] []
  | char : c ≠ '"' → c ≠ '\\' → Decodes cs vs → Decodes (c :: cs) (c :: vs)
  | escape : escapeValue e = some v → Decodes cs vs → Decodes ('\\' :: e :: cs) (v :: vs)

/-- The value of a STRING body, or `none` for a quote, a lone backslash or an
invalid escape. -/
def decodeBody : List Char → Option (List Char)
  | [] => some []
  | '\\' :: e :: rest =>
    match escapeValue e, decodeBody rest with
    | some v, some vs => some (v :: vs)
    | _, _ => none
  | '\\' :: [] => none
  | '"' :: _ => none
  | c :: rest => (decodeBody rest).map (c :: ·)

theorem decodeBody_iff {cs vs : List Char} : decodeBody cs = some vs ↔ Decodes cs vs := by
  constructor
  · intro found
    induction cs using decodeBody.induct generalizing vs with
    | case1 => simp only [decodeBody, Option.some.injEq] at found; subst found; exact .nil
    | case2 e rest v more decoded valued ih =>
      simp only [decodeBody, decoded, valued, Option.some.injEq] at found
      subst found
      exact .escape valued (ih decoded)
    | case3 e rest invalid ih =>
      simp only [decodeBody] at found
      cases found
    | case4 => simp [decodeBody] at found
    | case5 tail => simp [decodeBody] at found
    | case6 c rest backslash backslashEnd quote ih =>
      have plain : c ≠ '\\' := by
        intro h
        cases rest with
        | nil => exact backslashEnd h rfl
        | cons e more => exact backslash e more h rfl
      rw [decodeBody.eq_def] at found
      split at found
      · contradiction
      · rename_i e more same; cases same; exact absurd rfl plain
      · rename_i same; cases same; exact absurd rfl plain
      · rename_i tail same; cases same; exact absurd rfl quote
      · rename_i c' rest' _ _ _ same
        cases same
        obtain ⟨more, decoded, rfl⟩ := Option.map_eq_some_iff.mp found
        exact .char quote plain (ih decoded)
  · intro decodes
    induction decodes with
    | nil => rfl
    | char quote backslash _ ih =>
      rw [decodeBody.eq_def]
      split <;> simp_all
    | escape valued _ ih => simp [decodeBody, valued, ih]

/-- The value of a STRING spelling written with its quotes. -/
def decodeString (spelling : String) : Option String :=
  match spelling.toList with
  | '"' :: rest =>
    match rest.reverse with
    | '"' :: body => (decodeBody body.reverse).map String.ofList
    | _ => none
  | _ => none

/-- A STRING spelling has a value exactly when it is a quoted body whose
characters denote that value (MLS 3.7 A.1 S-CHAR and S-ESCAPE). -/
theorem decodeString_iff {spelling value : String} :
    decodeString spelling = some value ↔
      ∃ body, spelling.toList = '"' :: body ++ ['"'] ∧ Decodes body value.toList := by
  unfold decodeString
  constructor
  · intro found
    split at found
    · rename_i rest spelled
      split at found
      · rename_i body reversed
        obtain ⟨vs, decoded, rfl⟩ := Option.map_eq_some_iff.mp found
        refine ⟨body.reverse, ?_, by simpa using decodeBody_iff.mp decoded⟩
        rw [spelled, show rest = body.reverse ++ ['"'] by
          simpa using congrArg List.reverse reversed]
        rfl
      · cases found
    · cases found
  · rintro ⟨body, spelled, decodes⟩
    rw [spelled]
    simp only [List.cons_append, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.reverse_reverse]
    rw [decodeBody_iff.mpr decodes]
    simp

/-- A STRING body has a value. -/
theorem StringBody.decodes {body : List Char} (valid : StringBody body) : ∃ vs, Decodes body vs := by
  induction valid with
  | nil => exact ⟨[], .nil⟩
  | char quote backslash _ ih =>
    obtain ⟨vs, decodes⟩ := ih
    exact ⟨_, .char quote backslash decodes⟩
  | escape escaped _ ih =>
    obtain ⟨vs, decodes⟩ := ih
    obtain ⟨v, valued⟩ := Option.isSome_iff_exists.mp ((escapeValue_isSome _).trans escaped)
    exact ⟨_, .escape valued decodes⟩

/-- Every STRING the lexer takes has a value. -/
theorem string_decodes {cs : List Char} {n : Nat} (found : stringLength cs = some n) :
    ∃ value, decodeString (String.ofList ('"' :: cs.take n)) = some value := by
  obtain ⟨body, rest, rfl, valid, rfl⟩ := string_maximal.mp found
  obtain ⟨vs, decodes⟩ := valid.decodes
  refine ⟨String.ofList vs, decodeString_iff.mpr ⟨body, ?_, by simpa using decodes⟩⟩
  simp [List.take_append, List.take_of_length_le]

/-- A block comment ends at its first `*/`: comments do not nest, and a `/*`
inside a comment opens nothing. -/
theorem comment_not_nested {cs : List Char} {n : Nat} (found : blockCommentLength cs = some n) :
    ∃ body, cs.take n = body ++ ['*', '/'] ∧ ¬ ['*', '/'] <:+: body := by
  induction cs using blockCommentLength.induct generalizing n with
  | case1 => simp [blockCommentLength] at found
  | case2 rest =>
    simp only [blockCommentLength, Option.some.injEq] at found
    subst found
    exact ⟨[], rfl, by simp⟩
  | case3 c rest unclosed ih =>
    simp only [blockCommentLength, Option.map_eq_some_iff] at found
    obtain ⟨k, inner, rfl⟩ := found
    obtain ⟨body, taken, open'⟩ := ih inner
    refine ⟨c :: body, by simp [taken], ?_⟩
    intro inside
    rcases List.infix_cons_iff.mp inside with ⟨t, atHead⟩ | later
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at atHead
      obtain ⟨rfl, rfl⟩ := atHead
      cases rest with
      | nil => simp at taken
      | cons r rs =>
        cases k with
        | zero => simp at taken
        | succ k =>
          simp only [List.take_succ_cons, List.cons_append, List.cons.injEq] at taken
          exact unclosed rs rfl (by rw [taken.1])
    · exact open' later

/-- A quoted identifier is not scanned. -/
theorem quoted_identifier_rejected : ∃ d, lex "model 'q' end 'q';" = .error d := ⟨_, rfl⟩

end Rumoca
