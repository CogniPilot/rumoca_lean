import RumocaC.TreeTokenization

/-! Compose complete function fragments with independent grammars and maximal
tokenization. Actual continuations and boundaries between functions are kept
in the same witness; header and macro interpretation remain separate. -/
namespace Rumoca.CTree.Printer
open Syntax CTokens.PhaseSix

theorem function_sequence_renders (valid : ∀ fn ∈ functions, FunctionPrintable typedefs fn) :
    ∃ chunks, List.Forall₂ (FunctionPhrase typedefs) chunks functions ∧
      Closed chunks.flatten ∧ ∀ rest,
      CTokens.Prefix ((String.join (functions.map Function.render)).toList ++ rest) chunks.flatten rest := by
  induction functions with
  | nil => exact ⟨[], .nil, .empty, fun _ => .done⟩
  | cons fn functions ih =>
      obtain ⟨tokens, grammar, lexical⟩ := function_renders (valid fn (by simp))
      obtain ⟨chunks, grammars, closed, suffix⟩ := ih (fun f member => valid f (by simp [member]))
      refine ⟨tokens :: chunks, .cons grammar grammars, grammar.closed.append closed, ?_⟩
      intro rest
      have first := lexical ((String.join (functions.map Function.render)).toList ++ rest)
      have combined := first.append (suffix rest)
      simpa only [CString.join_toList, List.flatMap_map, Function.comp_def,
        List.flatMap_cons, List.flatten_cons, List.append_assoc] using combined

def FunctionsTokenization (typedefs : List String) (text : String) (functions : List Function) : Prop :=
    ∃ chunks, List.Forall₂ (FunctionPhrase typedefs) chunks functions ∧
      CTokens.Normal.Lexes text.toList chunks.flatten ∧
      ∀ output, Relation.ReflTransGen Rewrite chunks.flatten output → output = chunks.flatten

theorem function_sequence_tokenization (valid : ∀ fn ∈ functions, FunctionPrintable typedefs fn) :
    FunctionsTokenization typedefs (String.join (functions.map Function.render)) functions := by
  obtain ⟨chunks, grammars, closed, lexical⟩ := function_sequence_renders valid
  refine ⟨chunks, grammars, ?_, fun _ steps => closed.separated.unchanged steps⟩
  apply CTokens.Lexes.normal
  simpa only [List.append_nil] using lexical []

end Rumoca.CTree.Printer
