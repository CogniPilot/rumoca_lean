import Parser.Scanner.Prefix
import RumocaC.Tree

/-! C11 punctuator spellings and longest-match boundaries, independently of
the CTree renderer and its restricted scanner. The table is N1570 §6.4.6;
maximality follows §6.4p4. This judgment compares punctuators only: competing
preprocessing numbers, comments and other token categories are separate. -/
namespace Rumoca.CPunctuator

def spellings : List String :=
  ["[", "]", "(", ")", "{", "}", ".", "->", "++", "--", "&", "*", "+", "-", "~", "!",
    "/", "%", "<<", ">>", "<", ">", "<=", ">=", "==", "!=", "^", "|", "&&", "||",
    "?", ":", ";", "...", "=", "*=", "/=", "%=", "+=", "-=", "<<=", ">>=", "&=",
    "^=", "|=", ",", "#", "##", "<:", ":>", "<%", "%>", "%:", "%:%:"]

/-- An exact prefix with no longer punctuator spelling on the actual input. -/
structure Consumes (input : List Char) (spelling : String) (rest : List Char) : Prop where
  member : spelling ∈ spellings
  text : input = spelling.toList ++ rest
  longest : ∀ candidate ∈ spellings, candidate.toList <+: input →
    candidate.toList.length ≤ spelling.toList.length

theorem consumes_unique (first : Consumes input a restA) (second : Consumes input b restB) :
    a = b ∧ restA = restB := by
  have pa : a.toList <+: input := ⟨restA, first.text.symm⟩
  have pb : b.toList <+: input := ⟨restB, second.text.symm⟩
  have same : a.toList = b.toList :=
    (List.prefix_of_prefix_length_le pa pb (second.longest a first.member pa)).eq_of_length_le
      (first.longest b second.member pb)
  have strings : a = b := by simpa using congrArg String.ofList same
  refine ⟨strings, ?_⟩
  have texts := first.text.symm.trans second.text
  simpa only [strings, List.append_cancel_left_eq] using texts

/-- A separating space works for every C11 punctuator and every suffix. -/
theorem consumes_space (member : spelling ∈ spellings) (rest : List Char) :
    Consumes (spelling.toList ++ ' ' :: rest) spelling (' ' :: rest) := by
  refine ⟨member, rfl, ?_⟩
  intro candidate belongs starts
  have noSpace : ∀ word ∈ spellings, ' ' ∉ word.toList := by decide +kernel
  exact _root_.Parser.Scanner.prefix_before_delimiter starts (noSpace candidate belongs)

/-- A local boundary condition suffices even when the separator itself occurs
inside other punctuator spellings. It is checked against the independent table. -/
theorem consumes_boundary (member : spelling ∈ spellings)
    (stop : ∀ candidate ∈ spellings, ¬ spelling.toList ++ [next] <+: candidate.toList)
    (rest : List Char) :
    Consumes (spelling.toList ++ next :: rest) spelling (next :: rest) := by
  refine ⟨member, rfl, ?_⟩
  intro candidate belongs starts
  by_cases bounded : candidate.toList.length ≤ spelling.toList.length
  · exact bounded
  apply False.elim
  apply stop candidate belongs
  exact List.prefix_of_prefix_length_le
    (show spelling.toList ++ [next] <+: spelling.toList ++ next :: rest from
      ⟨rest, by simp⟩) starts (by simp only [List.length_append, List.length_singleton]; omega)

/-- Identifier characters are excluded from every C11 punctuator spelling. -/
theorem consumes_before_word (member : spelling ∈ spellings)
    (word : _root_.Parser.identRest next = true) (rest : List Char) :
    Consumes (spelling.toList ++ next :: rest) spelling (next :: rest) := by
  refine ⟨member, rfl, ?_⟩
  intro candidate belongs starts
  have nonword : ∀ token ∈ spellings, ∀ c ∈ token.toList,
      _root_.Parser.identRest c = false := by decide +kernel
  apply _root_.Parser.Scanner.prefix_before_delimiter starts
  intro includes
  have excluded := nonword candidate belongs next includes
  simp [word] at excluded

/-- Every punctuator stops before an opening parenthesis or an ordinary
string quote. CTree uses these boundaries for compound operands. -/
theorem consumes_before_operand (member : spelling ∈ spellings)
    (delimiter : next = '(' ∨ next = '"') (rest : List Char) :
    Consumes (spelling.toList ++ next :: rest) spelling (next :: rest) := by
  apply consumes_boundary member
  have all : ∀ token ∈ spellings, ∀ c ∈ ['(', '"'],
      ∀ candidate ∈ spellings, ¬ token.toList ++ [c] <+: candidate.toList := by
    decide +kernel
  exact all spelling member next (by simpa using delimiter)

/-- Spellings with no longer punctuator extension need no separator. -/
theorem consumes_unextendable (member : spelling ∈ spellings)
    (closed : ∀ candidate ∈ spellings, spelling.toList <+: candidate.toList → candidate = spelling)
    (rest : List Char) : Consumes (spelling.toList ++ rest) spelling rest := by
  refine ⟨member, rfl, ?_⟩
  intro candidate belongs starts
  rcases List.prefix_or_prefix_of_prefix starts (List.prefix_append spelling.toList rest) with
    before | after
  · exact before.length_le
  · simp [closed candidate belongs after]

/-- The structural separators used by CTree cannot grow into another C11
punctuator, even when the following expression has no leading whitespace. -/
theorem consumes_separator (member : spelling ∈ ["(", ")", "[", "]", "{", "}", ",", ";"])
    (rest : List Char) : Consumes (spelling.toList ++ rest) spelling rest := by
  apply consumes_unextendable
  · have all : ∀ word ∈ ["(", ")", "[", "]", "{", "}", ",", ";"], word ∈ spellings := by
      decide +kernel
    exact all spelling member
  · have all : ∀ word ∈ ["(", ")", "[", "]", "{", "}", ",", ";"],
        ∀ candidate ∈ spellings, word.toList <+: candidate.toList → candidate = word := by
      decide +kernel
    exact all spelling member

/-- This is the actual binary-operator renderer, with its emitted trailing
space. It cannot accidentally become a longer C punctuator. -/
theorem binop_consumes (op : CTree.BinOp) (rest : List Char) :
    Consumes (op.render.toList ++ ' ' :: rest) op.render (' ' :: rest) := by
  apply consumes_space
  cases op <;> decide +kernel

end Rumoca.CPunctuator
