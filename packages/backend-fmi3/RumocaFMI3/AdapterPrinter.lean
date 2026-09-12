import RumocaFMI3.RuntimePrinter
import RumocaFMI3.LiteralPreparation
import RumocaC.FunctionSequence

/-! Complete function-section grammar for the actual FMI adapter renderer.
The section is bound to the same prepared definition table as the call proofs.
Its fixed preamble still requires separate header/directive interpretation;
the lexical and phrase result does not imply scope/type or execution validity. -/
namespace Rumoca.FMI3.AdapterPrinter
open CTree CTree.Printer

theorem functions_printable (model : Solve.FMI3Model source) (signatures : List Signature)
    (valid : ∀ sig ∈ signatures, SignaturePrintable RuntimePrinter.typedefs sig) :
    ∀ fn ∈ LiteralPreparation.functions model signatures,
      FunctionPrintable RuntimePrinter.typedefs fn := by
  intro fn member
  change fn ∈ Runtime.helpers ++ signatures.map (Runtime.function model) at member
  rcases List.mem_append.mp member with helper | exported
  · exact RuntimePrinter.helpers_printable fn helper
  · obtain ⟨sig, sigMember, same⟩ := List.mem_map.mp exported
    subst fn
    exact RuntimePrinter.function_printable model sig (valid sig sigMember)

/-- Independent normal-context tokenization and per-function grammar for the
entire section following the fixed adapter preamble, in the actual file. -/
def FunctionsContract (model : Solve.FMI3Model source) (signatures : List Signature)
    (adapter : String) : Prop :=
  ∃ text, adapter = (functionPrefix model.name ++ "#include \"model.c\"\n" ++ Runtime.declarations) ++ text ∧
    FunctionsTokenization RuntimePrinter.typedefs text (LiteralPreparation.functions model signatures)

theorem rendered_contract (model : Solve.FMI3Model source) (signatures : List Signature)
    (valid : ∀ sig ∈ signatures, SignaturePrintable RuntimePrinter.typedefs sig) :
    FunctionsContract model signatures (Runtime.render model signatures) :=
  ⟨String.join ((LiteralPreparation.functions model signatures).map Function.render),
    LiteralPreparation.rendered_functions model signatures,
    function_sequence_tokenization (functions_printable model signatures valid)⟩

end Rumoca.FMI3.AdapterPrinter
