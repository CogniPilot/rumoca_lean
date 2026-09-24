import GALECParser.Parser
import RumocaCore.GALEC.Elaboration.Block.Preparation
import RumocaCore.GALEC.Elaboration.Static.Bounded

/-! One source parse feeds whole-block preparation under the target Integer
ceiling. No concrete source, backend or C certificate is required; parser
diagnostics are forwarded exactly and preparation failure is reported
separately. The pipeline never reparses or recognizes bodies by example. -/
namespace Rumoca.GALEC.Elaboration.Block
open _root_.Parser Rumoca.GALEC

structure Prepared (source : String) where
  parsed : Syntax.Parsed source
  result : Result
  prepared : Prepares Static.Bounded.integerCeiling parsed.ast result

def fromSource (source : String) : Except Diagnostic (Prepared source) :=
  match Syntax.parse source with
  | .error diagnostic => .error diagnostic
  | .ok parsed =>
    match lowered : fromBlock Static.Bounded.integerCeiling parsed.ast with
    | none => .error ⟨"GALEC preparation", 0, "outside the checked block preparation domain"⟩
    | some result => .ok ⟨parsed, result, (fromBlock_iff _ _ _).mp lowered⟩

/-- Exact successful result of one parse followed by the block preparer. The
right side is a proof specification, not a second runtime parse. -/
theorem erase_fromSource (source : String) :
    (fromSource source).toOption.map Prepared.result =
      ((Scanner.lex Syntax.scanner source).toOption.bind Structural.parse).bind
        (fromBlock Static.Bounded.integerCeiling) := by
  rw [← Syntax.erase_parse]
  unfold fromSource
  split
  · rename_i diagnostic failed
    simp only [failed, Except.toOption, Option.map_none, Option.bind_none]
  · rename_i parsed success
    simp only [success]
    split
    · rename_i failed
      simp [Except.toOption, failed]
    · rename_i result lowered
      simp [Except.toOption, lowered]

/-- Independent source provenance and whole-block preparation characterize
success for every source string and result; body examples are not the domain. -/
theorem fromSource_iff (source : String) (result : Result) :
    (∃ product, fromSource source = .ok product ∧ product.result = result) ↔
      ∃ block, Syntax.Witness source block ∧
        Prepares Static.Bounded.integerCeiling block result := by
  have option_iff : (fromSource source).toOption.map Prepared.result = some result ↔
      ∃ block, Syntax.Witness source block ∧
        Prepares Static.Bounded.integerCeiling block result := by
    rw [erase_fromSource, Option.bind_eq_some_iff]
    apply exists_congr
    intro block
    rw [← fromBlock_iff, ← Syntax.success_iff, ← Syntax.erase_parse]
    cases parsed : Syntax.parse source <;> simp [Except.toOption]
  rw [← option_iff]
  cases prepared : fromSource source <;> simp [Except.toOption]

theorem fromSource_parse_error (failed : Syntax.parse source = .error diagnostic) :
    fromSource source = .error diagnostic := by
  simp only [fromSource, failed]

end Rumoca.GALEC.Elaboration.Block
