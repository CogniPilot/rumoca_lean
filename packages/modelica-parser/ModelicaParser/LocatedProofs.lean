import ModelicaParser.LocatedParser

open _root_.Parser

/-! AST field provenance for the current action profile. These theorems bind
an accessor's range to the actual AST field, not merely to some equal text
elsewhere in the file. No proof module is imported by the editor runtime. -/
namespace Rumoca.LocatedParsed
variable {source : String}

theorem tokenSpan_text (p : LocatedParsed source) (index : Nat) (token : Token)
    (h : p.parsed.tokens[index]? = some token) :
    (p.tokenSpan index).text = token.text := by
  have he := congrArg (fun ts : List Token => ts[index]?) p.aligned.erases
  dsimp only at he
  rw [List.getElem?_map, h] at he
  cases hx : p.locations[index]? with
  | none => simp [hx] at he
  | some located =>
    have hv : located.value = token := by simpa [hx] using he
    have ht := p.lexemes located (List.mem_of_getElem? hx)
    simpa [tokenSpan, hx, hv] using ht

theorem modelName_text (p : LocatedParsed source) :
    (p.tokenSpan 1).text = p.parsed.ast.name := by
  apply p.tokenSpan_text 1 (.ident p.parsed.ast.name)
  rw [parseTokens_sound _ _ p.parsed.syntactic]
  rfl

theorem state_text (p : LocatedParsed source) :
    (p.tokenSpan 3).text = p.parsed.ast.state := by
  apply p.tokenSpan_text 3 (.ident p.parsed.ast.state)
  rw [parseTokens_sound _ _ p.parsed.syntactic]
  rfl

theorem derivativeName_text (p : LocatedParsed source) :
    (p.tokenSpan 8).text = p.parsed.ast.derivativeName := by
  apply p.tokenSpan_text 8 (.ident p.parsed.ast.derivativeName)
  rw [parseTokens_sound _ _ p.parsed.syntactic]
  rfl

theorem endName_text (p : LocatedParsed source) :
    (p.tokenSpan 14).text = p.parsed.ast.endName := by
  apply p.tokenSpan_text 14 (.ident p.parsed.ast.endName)
  rw [parseTokens_sound _ _ p.parsed.syntactic]
  rfl

theorem resolved_references (p : LocatedParsed source) (h : AST.Resolved p.parsed.ast) :
    (p.tokenSpan 8).text = (p.tokenSpan 3).text ∧
    (p.tokenSpan 14).text = (p.tokenSpan 1).text := by
  simp [p.derivativeName_text, p.state_text, p.endName_text, p.modelName_text,
    h.derivative_resolves, h.end_matches]

end Rumoca.LocatedParsed
