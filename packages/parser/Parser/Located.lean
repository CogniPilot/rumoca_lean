import Parser.Source
import Parser.Token

/-! Grammar-independent location attachment. The lexer chooses tokens; this
linear cursor pass checks their exact spelling against the immutable source.
No grammar rule or AST action supplies offsets. A later fused lexer can refine
this same contract without changing clients. -/
namespace Parser

namespace Source

variable {source : String}

/-- The entire gap is trivia; order is checked separately to exclude reversed
empty extracts. Comments are not admitted by the current lexical profiles. -/
def Gap (trivia : Char → Bool) (a b : source.Pos) : Prop :=
  a ≤ b ∧ (String.extract a b).toList.all trivia = true

instance (trivia : Char → Bool) (a b : source.Pos) : Decidable (Gap trivia a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Independent source alignment: tokens occur in order, exactly match their
source slices, and every intervening character (including EOF) is trivia. -/
inductive Aligned (trivia : Char → Bool) : source.Pos → List Token →
    List (Located source Token) → Prop where
  | nil : Gap trivia p source.endPos → Aligned trivia p [] []
  | cons : Gap trivia p span.start → span.text = t.text →
      Aligned trivia span.stop ts xs →
      Aligned trivia p (t :: ts) (⟨t, span⟩ :: xs)

theorem Aligned.erases (h : Aligned (source := source) trivia p ts xs) : xs.map (·.value) = ts := by
  induction h <;> simp_all

theorem Aligned.lexemes (h : Aligned (source := source) trivia p ts xs) :
    ∀ x ∈ xs, x.span.text = x.value.text := by
  induction h with
  | nil => simp
  | cons hg ht _ ih => simpa using And.intro ht ih

theorem Aligned.after (h : Aligned (source := source) trivia p ts xs) :
    ∀ x ∈ xs, p ≤ x.span.start := by
  induction h with
  | nil => simp
  | cons hg ht h ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hg.1
    · exact Nat.le_trans hg.1 (Nat.le_trans (Span.ordered _) (ih x hx))

theorem Aligned.disjoint (h : Aligned (source := source) trivia p ts xs) :
    xs.Pairwise (fun a b => a.span.stop ≤ b.span.start) := by
  induction h with
  | nil => exact .nil
  | cons _ _ tail ih => exact .cons tail.after ih

/-- The reversed prefix is data; its alignment continuation is a proof and is
erased. The recursive call returns directly, without rebuilding an `Option`
or a located-token list while unwinding the native stack. -/
def attachLoop (trivia : Char → Bool) (origin : source.Pos) (input : List Token)
    (p : source.Pos) (ts : List Token) (acc : List (Located source Token))
    (hprefix : ∀ xs, Aligned trivia p ts xs →
      Aligned trivia origin input (acc.reverse ++ xs)) :
    Option { xs : List (Located source Token) // Aligned trivia origin input xs } :=
  match ts with
  | [] => if h : Gap trivia p source.endPos then
      some ⟨acc.reverse, by simpa using hprefix [] (.nil h)⟩ else none
  | t :: ts =>
    let start := p.find (fun c => !trivia c)
    let stop := start.nextn t.text.length
    if hg : Gap trivia p start then
      if ho : start ≤ stop then
        let span : Span source := ⟨start, stop, ho⟩
        if ht : span.text = t.text then
          attachLoop trivia origin input stop ts (⟨t, span⟩ :: acc) (by
            intro xs h
            simpa using hprefix (⟨t, span⟩ :: xs) (.cons hg ht h))
        else none
      else none
    else none

/-- Tail-recursive attachment with the same exact source alignment contract.
Work is proportional to source and token spelling size; there is no search for
an identifier elsewhere in the document. Exact reference equivalence, including
failure, is proved in `Parser.LocatedProofs`. -/
def attach (trivia : Char → Bool) (p : source.Pos) (ts : List Token) :
    Option { xs : List (Located source Token) // Aligned trivia p ts xs } :=
  attachLoop trivia p ts p ts [] (by intro xs h; simpa using h)

/-- Additional context in the same immutable source snapshot. The enclosing
document supplies file identity; a grammar never invents paths or offsets. -/
structure RelatedInformation (source : String) where
  span : Span source
  message : String

structure Diagnostic (source : String) where
  phase : String
  span : Span source
  message : String
  related : List (RelatedInformation source) := []

/-- Character-offset lexer diagnostics are converted once at the API boundary.
The new public diagnostic carries valid UTF-8 positions. -/
def Diagnostic.ofCharacterOffset (source : String) (d : Parser.Diagnostic) : Diagnostic source :=
  let start := source.startPos.nextn d.offset
  let stop := start.nextn 1
  if h : start ≤ stop then ⟨d.phase, ⟨start, stop, h⟩, d.message, []⟩
  else ⟨d.phase, .point start, d.message, []⟩

structure Lexed (lexer : String → Except Parser.Diagnostic (List Token)) (source : String)
    (trivia : Char → Bool) where
  tokens : List (Located source Token)
  lexical : lexer source = .ok (tokens.map (·.value))
  aligned : Aligned trivia source.startPos (tokens.map (·.value)) tokens

def lexLocated (lexer : String → Except Parser.Diagnostic (List Token))
    (source : String) (trivia : Char → Bool := asciiSpace) :
    Except (Diagnostic source) (Lexed lexer source trivia) :=
  match hl : lexer source with
  | .error e => .error (.ofCharacterOffset source e)
  | .ok ts => match attach trivia source.startPos ts with
    | none => .error ⟨"location", .point source.startPos, "lexer/source alignment failed", []⟩
    | some xs => .ok ⟨xs.val, by rw [xs.property.erases]; exact hl,
        by simpa only [xs.property.erases] using xs.property⟩

end Source
end Parser
