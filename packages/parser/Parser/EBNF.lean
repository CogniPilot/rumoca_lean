import Parser.Token

/-! A small, total EBNF reader. Recursive expression semantics and checked
EBNF-to-CFG lowering are separate modules; there is no regular-rule expander.
Syntax: name = expression ; or the reference grammar's name : expression ;.
Single/double quoted terminals, IDENT, comma or whitespace sequences,
alternatives |, groups (), optionals [], repetitions {}, (* comments *) and
line comments are supported. Parol action annotations and regexes are not. -/
namespace Parser.EBNF

inductive Lexeme where
  | name (s : String)
  | text (s : String)
  | punct (c : Char)
  deriving Repr, BEq, DecidableEq

private def quoted (delimiter : Char) : List Char → Except String (String × List Char)
  | [] => .error "unterminated quoted terminal"
  | '\\' :: _ => .error "escapes in EBNF terminals are not supported"
  | c :: cs => do
    if c == delimiter then return ("", cs)
    let (s, tail) ← quoted delimiter cs
    return (String.singleton c ++ s, tail)

private def comment : List Char → Except String (List Char)
  | [] => .error "unterminated EBNF comment"
  | '*' :: ')' :: cs => .ok cs
  | _ :: cs => comment cs

private def tokenize : Nat → List Char → Except String (List Lexeme)
  | 0, _ => .error "EBNF input limit exceeded"
  | _ + 1, [] => .ok []
  | fuel + 1, cs@(c :: tail) => do
    if asciiSpace c then tokenize fuel tail
    else if cs.take 2 == ['(', '*'] then tokenize fuel (← comment (cs.drop 2))
    else if cs.take 2 == ['/', '/'] then tokenize fuel (cs.dropWhile (· != '\n'))
    else if c == '"' || c == '\'' then
      let (s, rest) ← quoted c tail
      return .text s :: (← tokenize fuel rest)
    else if identStart c then
      let word := cs.takeWhile identRest
      return .name (String.ofList word) :: (← tokenize fuel (cs.drop word.length))
    else if ['=', ':', ';', ',', '|', '(', ')', '[', ']', '{', '}'].contains c then
      return .punct c :: (← tokenize fuel tail)
    else .error s!"unexpected EBNF character {repr c}"

inductive Expr where
  | terminal (s : Symbol)
  | ref (name : String)
  | seq (a b : Expr)
  | alt (a b : Expr)
  | optional (a : Expr)
  | many (a : Expr)
  deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq

private def expect (c : Char) : List Lexeme → Except String (List Lexeme)
  | .punct d :: tail => if c == d then .ok tail else .error s!"expected '{c}'"
  | _ => .error s!"expected '{c}'"

private def startsPrimary : List Lexeme → Bool
  | .name _ :: _ | .text _ :: _ => true
  | .punct '(' :: _ | .punct '[' :: _ | .punct '{' :: _ => true
  | _ => false

mutual
  private def expression : Nat → List Lexeme → Except String (Expr × List Lexeme)
    | 0, _ => .error "EBNF nesting limit exceeded"
    | fuel + 1, input => do
      let (a, rest) ← sequence fuel input
      match rest with
      | .punct '|' :: tail =>
        let (b, tail) ← expression fuel tail
        return (.alt a b, tail)
      | _ => return (a, rest)

  private def sequence : Nat → List Lexeme → Except String (Expr × List Lexeme)
    | 0, _ => .error "EBNF nesting limit exceeded"
    | fuel + 1, input => do
      let (a, rest) ← primary fuel input
      match rest with
      | .punct ',' :: tail =>
        let (b, tail) ← sequence fuel tail
        return (.seq a b, tail)
      | _ =>
        if startsPrimary rest then
          let (b, tail) ← sequence fuel rest
          return (.seq a b, tail)
        else return (a, rest)

  private def primary : Nat → List Lexeme → Except String (Expr × List Lexeme)
    | 0, _ => .error "EBNF nesting limit exceeded"
    | _ + 1, .name "IDENT" :: tail => .ok (.terminal .ident, tail)
    | _ + 1, .name s :: tail => .ok (.ref s, tail)
    | _ + 1, .text s :: tail => .ok (.terminal (.literal s), tail)
    | fuel + 1, .punct '(' :: tail => do
      let (e, tail) ← expression fuel tail
      return (e, ← expect ')' tail)
    | fuel + 1, .punct '[' :: tail => do
      let (e, tail) ← expression fuel tail
      return (.optional e, ← expect ']' tail)
    | fuel + 1, .punct '{' :: tail => do
      let (e, tail) ← expression fuel tail
      return (.many e, ← expect '}' tail)
    | _, _ => .error "expected terminal, rule name, or group"
end

abbrev Grammar := List (String × Expr)

private def rules : Nat → List Lexeme → Except String Grammar
  | 0, _ => .error "EBNF rule limit exceeded"
  | _ + 1, [] => .ok []
  | fuel + 1, .name name :: .punct separator :: input => do
    if separator != '=' && separator != ':' then throw "expected rule = expression ; or rule : expression ;"
    if name == "IDENT" then throw "IDENT is a reserved lexical category"
    let (body, tail) ← expression (input.length * 4 + 4) input
    let rest ← rules fuel (← expect ';' tail)
    if rest.any (fun r => r.1 == name) then throw s!"duplicate rule {name}"
    return (name, body) :: rest
  | _, _ => .error "expected rule = expression ;"

def lex (source : String) : Except String (List Lexeme) :=
  tokenize (source.toList.length + 1) source.toList

def parseTokens (ts : List Lexeme) : Except String Grammar := do
  let g ← rules (ts.length + 1) ts
  if g.isEmpty then throw "empty grammar"
  return g

def parse (source : String) : Except String Grammar := do
  parseTokens (← lex source)

theorem parse_of_lex (h : lex source = .ok ts) : parse source = parseTokens ts := by
  unfold parse
  rw [h]
  rfl

end Parser.EBNF
