import ModelicaParser.LocatedParser
import Parser.LocatedCompleteness

/-! Location attachment covers every successful result of the actual Modelica
lexer. This adds no grammar and no extra acceptance hypothesis. -/
namespace Rumoca
open _root_.Parser

private theorem classifyWord_text (word : String) : (classifyWord word).text = word := by
  simp only [classifyWord]
  split <;> rfl

/-- The frontend's maximal-munch relation supplies the generic exact-spelling
contract. In particular, no emitted token starts with trivia. -/
theorem Lexes.spelled (lexical : Lexes cs ts) : Source.Spelled modelicaSpace cs ts := by
  induction lexical with
  | nil => exact .nil rfl
  | space hs _ ih => exact ih.space hs
  | @ident c ts cs hs hi _ ih =>
      have text : (classifyWord (String.ofList (c :: cs.takeWhile identRest))).text.toList =
          c :: cs.takeWhile identRest := by simp [classifyWord_text]
      have result := Source.Spelled.cons (gap := []) (by rfl) text hs ih
      simpa only [List.nil_append, text, List.cons_append, List.takeWhile_append_dropWhile] using result
  | @number c ts cs hs hi hd _ ih =>
      have text : (numberToken (c :: cs.takeWhile numberChar)).text.toList =
          c :: cs.takeWhile numberChar := by simp [numberToken_text]
      have result := Source.Spelled.cons (gap := []) (by rfl) text hs ih
      simpa only [List.nil_append, text, List.cons_append, List.takeWhile_append_dropWhile] using result
  | @punct c cs ts hs hi hd hp _ ih =>
      have text : (Token.literal (String.singleton c)).text.toList = [c] := by simp [Token.text]
      have result := Source.Spelled.cons (gap := []) (by rfl) text hs ih
      simpa only [List.nil_append, text, List.cons_append] using result
  | dotmul _ ih =>
      exact Source.Spelled.cons (gap := []) (by rfl) (t := .literal ".*") (c := '.')
        (chars := ['*']) rfl (by decide +kernel) ih

/-- Every certified parse has exact aligned token locations. -/
theorem Parsed.locations_exist (parsed : Parsed source) :
    ∃ xs, Source.attach modelicaSpace source.startPos parsed.tokens = some xs := by
  apply Source.attach_complete ((lex_correct source parsed.tokens).mp parsed.lexical).spelled
    source.startPos ""
  simp

end Rumoca
