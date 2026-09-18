import RumocaC.Punctuator
import RumocaC.PreprocessingNumber
import RumocaC.IdentifierToken
import RumocaC.StringEnvelope

/-! Compositional token judgments for the structured C printer. Each token is
checked with the actual continuation present. Numeric tokens retain their
spelling: constant value/range and C types belong to the phrase/typing contract.
Ordinary strings retain the independently decoded object bytes.

The word/punctuator guards exclude encoded-literal, dot-number and comment
fusion at fragment boundaries. Cross-category maximality, phase-six literal
concatenation and phrase grammar require their additional proofs. This module
defines no executable C parser or scanner. -/
namespace Rumoca.CTokens
open _root_.Parser

inductive Token where
  | word (name : String)
  | number (spelling : String)
  | string (object : List UInt8)
  | punctuator (spelling : String)
  deriving DecidableEq, Repr

def whitespace (c : Char) : Bool :=
  [' ', '\t', '\n', '\r', Char.ofNat 11, Char.ofNat 12].contains c

/-- Conservatively reserve both quote kinds after any C string-encoding prefix.
The printer supplies punctuation/space between such words and literals. -/
def EncodingSafe (name : String) (rest : List Char) : Prop :=
  name ∈ ["u8", "u", "U", "L"] →
    ∀ c tail, rest = c :: tail → c ≠ '"' ∧ c ≠ '\''

def PunctuationSafe (spelling : String) (rest : List Char) : Prop :=
  (spelling = "." → ∀ c tail, rest = c :: tail → c.isDigit = false) ∧
  (spelling = "/" → ∀ c tail, rest = c :: tail → c ≠ '/' ∧ c ≠ '*')

inductive Consumes : List Char → Token → List Char → Prop where
  | word : CIdentifierToken.WordParts name → CIdentifierToken.Consumes input name rest →
      EncodingSafe name rest → Consumes input (.word name) rest
  | number : CPPNumber.Spells spelling.toList → input = spelling.toList ++ rest →
      (∀ candidate, CPPNumber.Spells candidate → candidate <+: input →
        candidate.length ≤ spelling.toList.length) →
      Consumes input (.number spelling) rest
  | string : CString.Denotes text object → input = text ++ rest →
      Consumes input (.string object) rest
  | punctuator : CPunctuator.Consumes input spelling rest → PunctuationSafe spelling rest →
      Consumes input (.punctuator spelling) rest

inductive Prefix : List Char → List Token → List Char → Prop where
  | done : Prefix rest [] rest
  | space : whitespace c = true → Prefix cs ts rest → Prefix (c :: cs) ts rest
  | token : Consumes input token middle → Prefix middle tokens rest →
      Prefix input (token :: tokens) rest

def Lexes (text : List Char) (tokens : List Token) : Prop := Prefix text tokens []

theorem Prefix.append (first : Prefix input tokens middle) (second : Prefix middle more rest) :
    Prefix input (tokens ++ more) rest := by
  induction first with
  | done => exact second
  | space white tail ih => exact .space white (ih second)
  | token consumed tail ih => exact .token consumed (ih second)

theorem Prefix.finish (first : Prefix input tokens middle) (second : Lexes middle more) :
    Lexes input (tokens ++ more) := first.append second

theorem word_prefix (parts : CIdentifierToken.WordParts name)
    (stop : CLexical.identifierCharacter marker = false)
    (quote : marker ≠ '"') (characterQuote : marker ≠ '\'') (rest : List Char) :
    Prefix (name.toList ++ marker :: rest) [.word name] (marker :: rest) := by
  refine .token (.word parts (CIdentifierToken.word_consumes parts stop rest) ?_) .done
  intro encoding c tail same
  have chars := (List.cons.inj same).1
  exact chars ▸ ⟨quote, characterQuote⟩

theorem natural_prefix (n : Nat) (stop : CPPNumber.character marker = false) (rest : List Char) :
    Prefix ((toString n).toList ++ marker :: rest) [.number (toString n)] (marker :: rest) := by
  have number := CPPNumber.natural_consumes n stop rest
  exact .token (.number number.spelling number.input_eq number.longest) .done

/-- Any preprocessing-number spelling, followed by a character that cannot occur
in a preprocessing number, scans to a single number token. This covers the
floating-constant magnitudes `<digits>e<exponent>`, which the value relation for
plain decimals does not, and is the shared boundary used by the printer. -/
theorem number_prefix (spelling : String) (spelled : CPPNumber.Spells spelling.toList)
    (stop : CPPNumber.character marker = false) (rest : List Char) :
    Prefix (spelling.toList ++ marker :: rest) [.number spelling] (marker :: rest) := by
  refine .token (.number spelled rfl ?_) .done
  intro candidate cand starts
  apply Scanner.prefix_before_delimiter starts
  intro member
  have present := cand.characters marker member
  simp [stop] at present

theorem string_prefix (source : String) (rest : List Char) :
    Prefix ((CTree.quote source).toList ++ rest)
      [.string (source.toUTF8.data.toList ++ [0])] rest :=
  .token (.string (CString.quote_correct source) rfl) .done

theorem punctuator_prefix (read : CPunctuator.Consumes input spelling rest)
    (safe : PunctuationSafe spelling rest) : Prefix input [.punctuator spelling] rest :=
  .token (.punctuator read safe) .done

/-- These delimiters cannot extend to a longer punctuator, for any suffix. -/
theorem separator_prefix (member : spelling ∈ ["(", ")", "[", "]", "{", "}", ",", ";"])
    (rest : List Char) : Prefix (spelling.toList ++ rest) [.punctuator spelling] rest := by
  apply punctuator_prefix (CPunctuator.consumes_separator member rest)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [PunctuationSafe]

theorem Prefix.whitespaces (all : ∀ c ∈ chars, whitespace c = true)
    (tail : Prefix input tokens rest) : Prefix (chars ++ input) tokens rest := by
  induction chars with
  | nil => exact tail
  | cons c cs ih => exact .space (all c (by simp)) (ih (fun c member => all c (by simp [member])))

theorem Prefix.indent (count : Nat) (tail : Prefix input tokens rest) :
    Prefix (List.replicate count ' ' ++ input) tokens rest := by
  apply tail.whitespaces
  intro c member
  have eq : c = ' ' := (List.mem_replicate.mp member).2
  subst c
  decide +kernel

end Rumoca.CTokens
