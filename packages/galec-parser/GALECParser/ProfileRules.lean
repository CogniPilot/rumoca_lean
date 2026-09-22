import Parser.LALR.ActionWords
import GALECParser.StructuralActions
import GALECParser.ProfileProjection

namespace Rumoca.GALEC.Structural.ProfileSemantics
open _root_.Parser LALR.Frontend StructuralActions
open Structural

theorem lookup_reference : rules "reference" = some reference := rfl
theorem lookup_product : rules "product" = some product := rfl
theorem lookup_startup : rules "startup" = some startup := rfl
theorem lookup_recalibrate : rules "recalibrate" = some recalibrate := rfl
theorem lookup_doStep : rules "do_step" = some doStep := rfl
theorem lookup_tensorDoStep : rules "tensor_do_step" = some tensorDoStep := rfl
theorem lookup_scalarBlock : rules "block" = some scalarBlock := rfl
theorem lookup_tensorBlock : rules "tensor_block" = some tensorBlock := rfl
theorem lookup_program : rules "program" = some program := rfl

theorem symbol_literal (token : Token) (s : String) :
    token.symbol = .literal s ↔ token = .literal s := by
  cases token <;> simp [Token.symbol]

theorem terminal_words_literal (s : String) (word : List Token) (token : Token) :
    Words rules Token.symbol (.terminal (.literal s)) word token ↔
      word = [.literal s] ∧ token = .literal s := by
  rw [Words.terminal_iff, symbol_literal]
  constructor <;> rintro ⟨h, rfl⟩ <;> exact ⟨h, rfl⟩

end Rumoca.GALEC.Structural.ProfileSemantics

