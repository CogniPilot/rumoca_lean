import RumocaFMI3.DebugLoggingPrepared
import RumocaFMI3.DebugLoggingLegal
import RumocaFMI3.RuntimePrinter

/-! Required contract for the printed public setter and its prepared runtime.
The exact emitted tree is mandatory, rather than an assumption supplied by a
consumer of the actual-artifact certificate. -/
noncomputable section
namespace Rumoca.FMI3.DebugLogging
open CTree CLiteral

structure FunctionContract (model : Solve.FMI3Model source) (sigs : List Signature) (text : String) : Prop where
  member : signature ∈ sigs
  emitted : Runtime.function model signature = function
  printed : text = (Runtime.function model signature).render
  tokenization : Printer.FunctionTokenization RuntimePrinter.typedefs text (Runtime.function model signature)
  category : OnlyCategory (modelDescription model) "logStatus"
  prepared : ∀ pool, LiteralPreparation.prepare model sigs = some pool → PreparedContract model sigs pool

theorem rendered_contract (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature ∈ sigs) :
    FunctionContract model sigs (Runtime.function model signature).render := by
  refine ⟨member, function_eq model, rfl, ?_, described_category model,
    fun _ made => prepared_correct model sigs unique member (function_eq model) made⟩
  apply RuntimePrinter.function_tokenization
  refine ⟨Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)),
    by decide +kernel, ?_⟩
  intro param member
  simp only [signature, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals refine ⟨?_, by decide +kernel⟩
  all_goals first
    | exact Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel))
    | exact Syntax.TypeSpelling.const
        (show Syntax.TypeSpelling RuntimePrinter.typedefs "fmi3String" from
          Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)))

end Rumoca.FMI3.DebugLogging
end
