import RumocaC.TreeConcatenation
import RumocaC.Tokenization

/-! Composed lexical and phrase contract for the shared function printer.
The very same token sequence has independent maximal-token spelling, the
intended function tree and stability under ordinary-string concatenation.
Header names and macro expansion require their separate context contracts. -/
namespace Rumoca.CTree.Printer

def FunctionTokenization (typedefs : List String) (text : String) (function : Function) : Prop :=
  ∃ tokens, CTokens.Normal.Lexes text.toList tokens ∧
    Syntax.FunctionPhrase typedefs tokens function ∧
    ∀ output, Relation.ReflTransGen CTokens.PhaseSix.Rewrite tokens output → output = tokens

theorem FunctionDenotes.tokenization (contract : FunctionDenotes typedefs text function) :
    FunctionTokenization typedefs text function := by
  obtain ⟨tokens, lexical, grammar, unchanged⟩ := contract.phase_six
  exact ⟨tokens, lexical.normal, grammar, unchanged⟩

end Rumoca.CTree.Printer
