import ModelicaParser.LocatedParser

open _root_.Parser

/-! AST field provenance for the current action profile. These theorems bind
an accessor's range to the actual AST field, not merely to some equal text
elsewhere in the file. No proof module is imported by the editor runtime. -/
namespace Rumoca.LocatedParsed
variable {source : String}

theorem fieldSpan_eq_tokenSpan (p : LocatedParsed source) (index : Fin 16) :
    p.fieldSpan index = p.tokenSpan index.val := by
  have bound : index.val < p.locations.length := by
    rw [p.location_count]
    exact index.isLt
  simp [fieldSpan, tokenSpan, List.getElem?_eq_getElem bound]

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

theorem state_field_text (p : LocatedParsed source) :
    (p.fieldSpan 3).text = p.parsed.ast.state := by
  rw [p.fieldSpan_eq_tokenSpan]
  exact p.state_text

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

/-- Enriching diagnostics preserves every successful resolution. -/
theorem resolve_complete (p : LocatedParsed source) (h : AST.Resolved p.parsed.ast) :
    p.resolve = .ok ⟨h⟩ := by
  simp [resolve, AST.resolve_complete _ h]

/-- Every name error identifies the offending AST occurrence and its actual
declaration, including the source text at both ranges. End-name disagreement
takes precedence when both names are wrong. No search for equal text is used. -/
theorem resolve_error_locations (p : LocatedParsed source) (e : Source.Diagnostic source)
    (h : p.resolve = .error e) :
    e.phase = "resolve" ∧
      ((p.parsed.ast.endName ≠ p.parsed.ast.name ∧
        e.span = p.tokenSpan 14 ∧ e.span.text = p.parsed.ast.endName ∧
        e.related.map (·.span) = [p.tokenSpan 1] ∧
        e.related.map (fun note => note.span.text) = [p.parsed.ast.name]) ∨
       (p.parsed.ast.endName = p.parsed.ast.name ∧
        p.parsed.ast.derivativeName ≠ p.parsed.ast.state ∧
        e.span = p.tokenSpan 8 ∧ e.span.text = p.parsed.ast.derivativeName ∧
        e.related.map (·.span) = [p.tokenSpan 3] ∧
        e.related.map (fun note => note.span.text) = [p.parsed.ast.state])) := by
  by_cases hn : p.parsed.ast.endName = p.parsed.ast.name
  · by_cases hd : p.parsed.ast.derivativeName = p.parsed.ast.state
    · simp [resolve, AST.resolve, hn, hd] at h
    · simp only [resolve, AST.resolve, hn, hd, ↓reduceDIte, ↓reduceIte,
        Except.error.injEq] at h
      subst e
      exact ⟨rfl, .inr ⟨hn, hd, rfl, p.derivativeName_text, rfl,
        by simp [p.state_text]⟩⟩
  · simp only [resolve, AST.resolve, hn, ↓reduceDIte, ↓reduceIte,
      Except.error.injEq] at h
    subst e
    exact ⟨rfl, .inl ⟨hn, rfl, p.endName_text, rfl,
      by simp [p.modelName_text]⟩⟩

end Rumoca.LocatedParsed
