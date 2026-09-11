import Parser.Scanner
import Parser.LocatedCompleteness

/-! Exact-spelling attachment contract for reusable scanner configurations.
Word classifiers must preserve the spelling; trivia and token shapes are
otherwise supplied by the configuration, without language-specific imports. -/
namespace Parser.Scanner

/-- Successful maximal-munch derivations satisfy the location contract whenever
word classification retains the original text. Single/pair symbols and numeric
spellings are handled by the scanner itself. -/
theorem Lexes.spelled (classified : ∀ word, (cfg.classify word).text = word)
    (lexical : Lexes cfg cs ts) : Source.Spelled cfg.space cs ts := by
  induction lexical with
  | nil => exact .nil rfl
  | space hs _ ih => exact ih.space hs
  | @word c ts cs hs hw _ ih =>
      have text : (cfg.classify (String.ofList (c :: cs.takeWhile cfg.wordRest))).text.toList =
          c :: cs.takeWhile cfg.wordRest := by simp [classified]
      have result := Source.Spelled.cons (gap := []) (by rfl) text hs ih
      simpa only [List.nil_append, text, List.cons_append, List.takeWhile_append_dropWhile] using result
  | @number c ts cs hs hw hd _ ih =>
      have text : (Token.literal (String.ofList (c :: cs.takeWhile cfg.numberRest))).text.toList =
          c :: cs.takeWhile cfg.numberRest := by simp [Token.text]
      have result := Source.Spelled.cons (gap := []) (by rfl) text hs ih
      simpa only [List.nil_append, text, List.cons_append, List.takeWhile_append_dropWhile] using result
  | @symbol c cs t rest ts hs hw hd symbol _ ih =>
      cases symbol with
      | @single c cs hp single =>
          have text : (Token.literal (String.singleton c)).text.toList = [c] := by simp [Token.text]
          have result := Source.Spelled.cons (gap := []) (by rfl) text hs ih
          simpa only [List.nil_append, text, List.cons_append] using result
      | @pair c d cs pair =>
          have text : (Token.literal (String.ofList [c, d])).text.toList = [c, d] := by simp [Token.text]
          have result := Source.Spelled.cons (gap := []) (by rfl) text hs ih
          simpa only [List.nil_append, text, List.cons_append] using result

/-- No successful tokenization of a spelling-preserving scanner configuration
can fail source attachment. This is independent of a particular AST or grammar. -/
theorem lex_locations (cfg : Config) (classified : ∀ word, (cfg.classify word).text = word)
    (source : String) (tokens : List Token) (accepted : lex cfg source = .ok tokens) :
    ∃ xs, Source.attach cfg.space source.startPos tokens = some xs := by
  apply Source.attach_complete ((lex_correct cfg source tokens).mp accepted |>.spelled classified)
    source.startPos ""
  simp

end Parser.Scanner
