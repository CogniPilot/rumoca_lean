import RumocaC.PrinterCertificate
import ProofAudit.Audit
open Lean Elab Command
open Rumoca.CTree.Printer.Certificate

#audit axioms Rumoca.CTree.Printer.Certificate.signatureProof
#audit axioms Rumoca.CTree.Printer.Certificate.signaturesProof
#audit axioms Rumoca.CTree.Printer.Certificate.characterBlockSize
#audit axioms Rumoca.CTree.Printer.Certificate.quoteCharacters
#audit axioms Rumoca.CTree.Printer.Certificate.remainingCharacters
#audit axioms Rumoca.CTree.Printer.Certificate.checkCharacterEquality
#audit axioms Rumoca.CTree.Printer.Certificate.certifyConcatenation

-- Compilation checks instance availability from the lower owner alone.
example : ToExpr Rumoca.CTree.BinOp := inferInstance
example : ToExpr Rumoca.CTree.Expr := inferInstance
example : ToExpr Rumoca.CTree.Stmt := inferInstance
example : ToExpr Rumoca.CTree.Parameter := inferInstance
example : ToExpr Rumoca.CTree.Signature := inferInstance
example : ToExpr Rumoca.CTree.Function := inferInstance

-- Focused infrastructure check, not an actual-file or universal emitter claim.
elab "check_quotation_factor" : command => do
  let actual ← quoteCharacters `QuotationCheck.input "ab"
  let a ← quoteCharacters `QuotationCheck.first "a"
  let b ← quoteCharacters `QuotationCheck.second "b"
  discard <| certifyConcatenation `QuotationCheck.assembly actual #[a, b] #[1, 1]
  let empty ← quoteCharacters `QuotationCheck.emptyInput ""
  discard <| certifyConcatenation `QuotationCheck.emptyAssembly empty #[] #[]

check_quotation_factor

#audit axioms QuotationCheck.assembly.joined_0
#audit axioms QuotationCheck.assembly.empty
#audit axioms QuotationCheck.emptyAssembly.joined_end
