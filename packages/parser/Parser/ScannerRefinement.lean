import Parser.Scanner

/-! Exact refinement for configurations that used the scanner before shared
single/pair prefixes were enabled. The reference is proof-only and includes
failure messages and offsets, not only the successfully recognized language. -/
namespace Parser.Scanner

namespace StrictReference
noncomputable section

def readSymbol (cfg : Config) : List Char → Option (Token × List Char)
  | [] => none
  | c :: cs => match cfg.pair c with
    | none => if cfg.single c then some (.literal (String.singleton c), cs) else none
    | some d => match cs with
      | [] => none
      | e :: es => if e = d then some (.literal (String.ofList [c, d]), es) else none

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

def lex (cfg : Config) (source : String) : Except Diagnostic (List Token) :=
  scan cfg source.toList.length (source.toList.length + 1) source.toList

end
end StrictReference

theorem scan_disjoint (cfg : Config)
    (disjoint : ∀ c, cfg.single c = true → cfg.pair c = none)
    (total fuel : Nat) (chars : List Char) :
    scan cfg total fuel chars = StrictReference.scan cfg total fuel chars := by
  induction fuel generalizing chars with
  | zero => rfl
  | succ fuel ih =>
      cases chars with
      | nil => rfl
      | cons c rest =>
          have symbols : readSymbol cfg (c :: rest) = StrictReference.readSymbol cfg (c :: rest) :=
            readSymbol_disjoint cfg disjoint _
          simp only [scan, StrictReference.scan, ih, symbols]
          rfl

theorem lex_disjoint (cfg : Config)
    (disjoint : ∀ c, cfg.single c = true → cfg.pair c = none) (source : String) :
    lex cfg source = StrictReference.lex cfg source :=
  scan_disjoint cfg disjoint _ _ _

end Parser.Scanner
