import Parser.LALR.EBNFSoundness
import Parser.LALR.EBNFCompleteness
import Parser.LALR.DerivationTrees

/-! Reflection through the finite terminal encoding. Unknown input symbols
map outside the grammar alphabet and cannot alias a grammar token or EOF. -/
namespace Parser.LALR.Frontend

variable {p : Prepared}

/-- Every in-range token encoding decodes to the exact original symbol. This
holds even if the candidate alphabet contains duplicate entries. -/
theorem Prepared.decode_encode (valid : p.encode symbol < p.alphabet.size) :
    p.decode (p.encode symbol) = symbol := by
  cases found : p.alphabet.findIdx? (· == symbol) with
  | none =>
    simp only [Prepared.encode, found, Option.getD_none] at valid
    omega
  | some code =>
    obtain ⟨bound, same, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp found
    have same := eq_of_beq same
    simp only [Prepared.encode, found, Option.getD_some, Prepared.decode,
      Array.getElem?_eq_getElem bound, Option.getD_some, same]

/-- Well-formed CFGs derive only terminals from their declared alphabet. -/
theorem accepted_tokens_valid {g : Grammar} (wf : g.wellFormed = true)
    (accepted : g.Accepts word) : ∀ token ∈ word, token < g.terminals := by
  have initial : ∀ symbol ∈ [.nonterminal g.start], g.atomValid symbol = true := by
    intro symbol member
    obtain rfl := List.mem_singleton.mp member
    have bounds := wf
    simp only [Grammar.wellFormed, Bool.and_eq_true] at bounds
    exact bounds.1
  have result := g.derives_valid wf accepted initial
  intro token member
  have valid := result (.terminal token) (List.mem_map.mpr ⟨token, member, rfl⟩)
  exact of_decide_eq_true valid

/-- Exact language equivalence at the external token-symbol boundary. The
source side contains neither the CFG, the lowering algorithm nor parser fuel. -/
theorem Witness.accepts_iff {w : Witness} {source : EBNF.Grammar}
    (checked : w.Conditions source p) (wf : p.grammar.wellFormed = true)
    (word : List Parser.Symbol) :
    EBNF.Accepts source word ↔ p.grammar.Accepts (word.map p.encode) := by
  constructor
  · exact w.accepts_encoded checked
  · intro accepted
    have reflected := w.accepts_decoded checked accepted
    have valid := accepted_tokens_valid wf accepted
    have same : (word.map p.encode).map p.decode = word := by
      rw [List.map_map]
      have pointwise : ∀ symbol ∈ word, (p.decode ∘ p.encode) symbol = id symbol := by
        intro symbol member
        apply Prepared.decode_encode
        rw [← checked.2.2.1]
        exact valid (p.encode symbol) (List.mem_map.mpr ⟨symbol, member, rfl⟩)
      exact (List.map_congr_left pointwise).trans (List.map_id _)
    simpa only [same] using reflected

end Parser.LALR.Frontend
