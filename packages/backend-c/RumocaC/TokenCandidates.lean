import RumocaC.Tokens

/-! Independent competing-token envelope for ordinary C11 code (N1570 §6.4).
Header-name recognition belongs to include/pragma contexts and is excluded
here. The encoded/character cases deliberately overapproximate non-emitted
literal classes by their required prefixes; the residual singleton includes
every character. These are competitors for a length bound, not acceptance
rules or execution meanings. Ordinary strings, identifiers and pp-numbers
reuse their reviewed envelopes. Comments have a separate start predicate.

The emitted-token spelling and maximal-token judgments below do not refer to
CTree rendering or the Consumes constructor proofs. -/
namespace Rumoca.CTokens.Normal

inductive Candidate : List Char → Prop where
  | identifier : CIdentifierToken.Spells chars → Candidate chars
  | number : CPPNumber.Spells chars → Candidate chars
  | string : CString.Quoted chars → Candidate chars
  | encoded : encoding ∈ ["u8", "u", "U", "L"] → marker ∈ ['"', '\''] →
      Candidate (encoding.toList ++ marker :: rest)
  | character : Candidate ('\'' :: rest)
  | punctuator : spelling ∈ CPunctuator.spellings → Candidate spelling.toList
  | singleton (c : Char) : Candidate [c]

/-- The independently specified spellings and object bytes of emitted tokens. -/
inductive Spelling : Token → List Char → Prop where
  | word : CIdentifierToken.WordParts name → Spelling (.word name) name.toList
  | number : CPPNumber.Spells spelling.toList → Spelling (.number spelling) spelling.toList
  | string : CString.Denotes chars bytes → Spelling (.string bytes) chars
  | punctuator : name ∈ CPunctuator.spellings → Spelling (.punctuator name) name.toList

def Longest (input chars : List Char) : Prop :=
  ∀ candidate, Candidate candidate → candidate <+: input → candidate.length ≤ chars.length

def CommentStart (chars : List Char) : Prop :=
  ∃ rest, chars = '/' :: '/' :: rest ∨ chars = '/' :: '*' :: rest

/-- One normal-context emitted token, with all competing token classes checked
against the actual continuation and with a comment opener excluded. -/
def Consumes (input : List Char) (token : Token) (rest : List Char) : Prop :=
  ∃ chars, Spelling token chars ∧ input = chars ++ rest ∧ Longest input chars ∧ ¬ CommentStart input

/-- Comment-free tokenization of the printed subset in an ordinary-code
context. Header names, preprocessing directives and macro expansion are not
interpreted by this relation. It is a declarative specification only. -/
inductive Prefix : List Char → List Token → List Char → Prop where
  | done : Prefix rest [] rest
  | space : whitespace c = true → Prefix cs ts rest → Prefix (c :: cs) ts rest
  | token : Consumes input token middle → Prefix middle tokens rest →
      Prefix input (token :: tokens) rest

def Lexes (text : List Char) (tokens : List Token) : Prop := Prefix text tokens []

end Rumoca.CTokens.Normal
