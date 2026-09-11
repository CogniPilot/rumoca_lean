import Parser.Scanner

/-! Shared ASCII C identifiers and lexical facts. Each target adds its own
typedef names to the C11 keywords; no source-language name resolution occurs. -/
namespace Rumoca.CIdentifier
open _root_.Parser

def keywords : List String :=
  ["auto", "break", "case", "char", "const", "continue", "default", "do", "double",
   "else", "enum", "extern", "float", "for", "goto", "if", "inline", "int", "long",
   "register", "restrict", "return", "short", "signed", "sizeof", "static", "struct",
   "switch", "typedef", "union", "unsigned", "void", "volatile", "while", "_Alignas",
   "_Alignof", "_Atomic", "_Bool", "_Complex", "_Generic", "_Imaginary", "_Noreturn",
   "_Static_assert", "_Thread_local"]

def valid (reserved : List String) (name : String) : Bool := match name.toList with
  | [] => false
  | c :: cs => identStart c && cs.all identRest && !(keywords ++ reserved).contains name

theorem word_parts (reserved : List String) (name : String) (h : valid reserved name = true) :
    ∃ c cs, name.toList = c :: cs ∧ identStart c = true ∧ cs.all identRest = true := by
  unfold valid at h
  split at h
  · contradiction
  · rename_i c cs hc
    simp only [Bool.and_eq_true] at h
    exact ⟨c, cs, hc, h.1.1, h.1.2⟩

private theorem ident_not_space {c : Char} (h : identStart c = true) : asciiSpace c = false := by
  apply Bool.eq_false_iff.mpr
  intro hs
  simp only [asciiSpace, Bool.or_eq_true, beq_iff_eq] at hs
  rcases hs with ((rfl | rfl) | rfl) | rfl <;> contradiction

private theorem take_word (word rest : List Char) (c : Char)
    (h : word.all identRest = true) (stop : identRest c = false) :
    (word ++ c :: rest).takeWhile identRest = word ∧
      (word ++ c :: rest).dropWhile identRest = c :: rest := by
  induction word with
  | nil => simp [stop]
  | cons a word ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨ht, hd⟩ := ih h.2
    simp [h.1, ht, hd]

theorem lex_word (cfg : Scanner.Config) (space : cfg.space = asciiSpace)
    (start : cfg.wordStart = identStart) (tail : cfg.wordRest = identRest)
    (classify : cfg.classify = Token.literal)
    (name : String) (c : Char) (rest : List Char) (ts : List Token)
    (parts : ∃ head tail, name.toList = head :: tail ∧ identStart head = true ∧ tail.all identRest = true)
    (stop : identRest c = false) (h : Scanner.Lexes cfg (c :: rest) ts) :
    Scanner.Lexes cfg (name.toList ++ c :: rest) (.literal name :: ts) := by
  obtain ⟨head, chars, hn, hs, ht⟩ := parts
  obtain ⟨take, drop⟩ := take_word chars rest c ht stop
  have nameEq : String.ofList (head :: chars) = name := by rw [← hn, String.ofList_toList]
  rw [hn]
  have step := Scanner.Lexes.word (cfg := cfg) (cs := chars ++ c :: rest)
    (space ▸ ident_not_space hs) (start ▸ hs) (by simpa only [tail, drop] using h)
  simpa only [tail, take, classify, nameEq, List.cons_append] using step

end Rumoca.CIdentifier

/-- Build fixed C lexical fragments from the independent scanner relation. -/
macro "c_lex_fixed" : tactic => `(tactic|
  repeat first
  | assumption
  | exact _root_.Parser.Scanner.Lexes.nil
  | apply _root_.Parser.Scanner.Lexes.space (by decide +kernel)
  | apply _root_.Parser.Scanner.Lexes.word (by decide +kernel) (by decide +kernel)
  | apply _root_.Parser.Scanner.Lexes.number (by decide +kernel) (by decide +kernel) (by decide +kernel)
  | apply _root_.Parser.Scanner.Lexes.symbol (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (_root_.Parser.Scanner.SymbolLexes.single_unpaired (by decide +kernel) (by decide +kernel))
  | apply _root_.Parser.Scanner.Lexes.symbol (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (_root_.Parser.Scanner.SymbolLexes.pair (by decide +kernel)))
