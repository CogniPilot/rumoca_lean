import RumocaC.FunctionPrinter
import Lean

/-! Candidate proof construction for raw C signature spellings. The caller
supplies the typedef context and the actual signature data. This tool proposes
applications of the shared printer theorems, never an assumed type meaning or
parser result. The kernel must check the resulting SignaturePrintable judgment;
unsupported spellings fail certification. No file I/O is performed here. -/
namespace Rumoca.CTree.Printer.Certificate
open Lean Elab Command

private def typeProof (typedefs : TSyntax `term) : Nat → String → CommandElabM (TSyntax `term)
  | 0, _ => throwError "type spelling exceeds certificate budget"
  | fuel + 1, text => do
      if text.startsWith "const " then
        let tail := (text.drop 6).toString
        let proof ← typeProof typedefs fuel tail
        return ← `(term| CTree.Syntax.TypeSpelling.const $proof)
      if text.endsWith " *" then
        let tail := (text.dropEnd 2).toString
        let proof ← typeProof typedefs fuel tail
        return ← `(term| CTree.Syntax.TypeSpelling.pointer $proof)
      let name := Lean.Syntax.mkStrLit text
      if text ∈ ["void", "char", "int", "double"] then
        return ← `(term| (CTree.Syntax.TypeSpelling.named
          (.primitive (by decide +kernel)) : CTree.Syntax.TypeSpelling $typedefs $name))
      return ← `(term| (CTree.Syntax.TypeSpelling.named
        (.typedefName (by decide +kernel) (by decide +kernel)) : CTree.Syntax.TypeSpelling $typedefs $name))

def signatureProof (typedefs : TSyntax `term) (sig : CTree.Signature) :
    CommandElabM (TSyntax `term) := do
  let result ← typeProof typedefs (sig.result.length + 1) sig.result
  let mut parameters ← `(term| ((by intro param absent; cases absent) :
    ∀ param ∈ ([] : List CTree.Parameter), CTree.Printer.ParameterPrintable $typedefs param))
  for param in sig.parameters.reverse do
    let type ← typeProof typedefs (param.type.length + 1) param.type
    parameters ← `(term| List.forall_mem_cons.mpr ⟨⟨$type, by decide +kernel⟩, $parameters⟩)
  `(term| ⟨$result, by decide +kernel, $parameters⟩)

def signaturesProof (typedefs : TSyntax `term) (signatures : List CTree.Signature) :
    CommandElabM (TSyntax `term) := do
  let mut all ← `(term| ((by intro sig absent; cases absent) :
    ∀ sig ∈ ([] : List CTree.Signature), CTree.Printer.SignaturePrintable $typedefs sig))
  for sig in signatures.reverse do
    let proof ← signatureProof typedefs sig
    all ← `(term| List.forall_mem_cons.mpr ⟨$proof, $all⟩)
  return all

end Rumoca.CTree.Printer.Certificate
