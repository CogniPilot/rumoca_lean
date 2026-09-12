import Parser.LALR.EBNFWitness

/-! Reflection of CFG derivations into the independent recursive EBNF
semantics. Every actual production is justified by a finite structural
annotation. The proof quantifies over arbitrary grammars and derivations. -/
namespace Parser.LALR.Frontend

/-- Decoding is used only with terminal identities checked by the witness.
Its default cannot justify an incorrectly annotated terminal production. -/
def Prepared.decode (p : Prepared) (code : Nat) : Parser.Symbol :=
  p.alphabet[code]?.getD .ident

def AtomYields (source : EBNF.Grammar) (p : Prepared) (meanings : Meanings) :
    Atom → List Parser.Symbol → Prop
  | .terminal t, word => word = [p.decode t]
  | .nonterminal n, word =>
      ∃ expr, meanings[n]? = some expr ∧ EBNF.Derives source expr word

inductive Yields (source : EBNF.Grammar) (p : Prepared) (meanings : Meanings) :
    List Atom → List Parser.Symbol → Prop where
  | nil : Yields source p meanings [] []
  | cons {symbol symbols word words}
      (head : AtomYields source p meanings symbol word)
      (tail : Yields source p meanings symbols words) :
      Yields source p meanings (symbol :: symbols) (word ++ words)

variable {source : EBNF.Grammar} {p : Prepared} {meanings : Meanings}

@[simp] theorem Yields.nil_iff : Yields source p meanings [] word ↔ word = [] := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil

@[simp] theorem Yields.singleton_iff :
    Yields source p meanings [symbol] word ↔ AtomYields source p meanings symbol word := by
  constructor
  · intro h
    cases h with
    | cons head tail =>
      have empty := Yields.nil_iff.mp tail
      simpa only [empty, List.append_nil] using head
  · intro h
    simpa only [List.append_nil] using Yields.cons h (.nil (source := source))

theorem Yields.append (left : Yields source p meanings a first)
    (right : Yields source p meanings b second) :
    Yields source p meanings (a ++ b) (first ++ second) := by
  induction left with
  | nil => exact right
  | cons head tail ih =>
    simpa only [List.cons_append, List.append_assoc] using Yields.cons head ih

theorem Yields.append_iff : Yields source p meanings (a ++ b) word ↔
    ∃ first second, word = first ++ second ∧
      Yields source p meanings a first ∧ Yields source p meanings b second := by
  constructor
  · intro h
    induction a generalizing word with
    | nil => exact ⟨[], word, rfl, .nil, h⟩
    | cons x xs ih =>
      cases h with
      | @cons _ _ headWord tailWord head tail =>
        obtain ⟨first, second, rfl, hl, hr⟩ := ih tail
        exact ⟨headWord ++ first, second, (List.append_assoc ..).symm,
          .cons head hl, hr⟩
  · rintro ⟨first, second, rfl, hl, hr⟩
    exact hl.append hr

/-- Reading the sentential form of a checked fragment recovers its EBNF
expression. Helper nonterminals use their explicit expression meanings. -/
theorem Fragment.yields (f : Fragment) (checked : f.Interprets p meanings)
    (yield : Yields source p meanings f.rhs word) : EBNF.Derives source f.expr word := by
  induction f generalizing word with
  | empty =>
    have empty := Yields.nil_iff.mp yield
    subst word
    exact .empty
  | terminal symbol code =>
    have same := Yields.singleton_iff.mp yield
    change word = [p.decode code] at same
    have decode : p.decode code = symbol := by
      simp only [Prepared.decode, checked.1, Option.getD_some]
    simpa only [same, decode, Fragment.expr] using EBNF.Derives.terminal checked.2.2
  | ref name n | alt n a b | optional n a | many n a =>
    obtain ⟨expr, lookup, derives⟩ := Yields.singleton_iff.mp yield
    have same := Option.some.inj (checked.symm.trans lookup)
    simpa only [← same] using derives
  | seq a b ih ihb =>
    obtain ⟨first, second, rfl, hl, hr⟩ := Yields.append_iff.mp yield
    exact .seq (ih checked.1 hl) (ihb checked.2 hr)

/-- Each annotation justifies one actual production, including epsilon and
recursive repetition. No parser or finite token example enters this lemma. -/
theorem AnnotatedRule.yields (rule : AnnotatedRule)
    (checked : rule.Valid source p meanings)
    (yield : Yields source p meanings rule.production.output word) :
    AtomYields source p meanings (.nonterminal rule.production.input) word := by
  refine ⟨rule.meaning, checked.1, ?_⟩
  cases rule with
  | named n name body =>
    exact .ref checked.2.1 (body.yields checked.2.2 yield)
  | altLeft n a b => exact .altLeft (a.yields checked.2 yield)
  | altRight n a b => exact .altRight (b.yields checked.2 yield)
  | optionalEmpty n body =>
    have empty := Yields.nil_iff.mp yield
    subst word
    exact .optionalEmpty
  | optionalSome n body => exact .optionalSome (body.yields checked.2 yield)
  | manyEmpty n body =>
    have empty := Yields.nil_iff.mp yield
    subst word
    exact .manyEmpty
  | manyCons n body =>
    obtain ⟨first, rest, rfl, head, tail⟩ := Yields.append_iff.mp yield
    obtain ⟨expr, lookup, derives⟩ := Yields.singleton_iff.mp tail
    have same := Option.some.inj (checked.1.symm.trans lookup)
    exact .manyCons (body.yields checked.2 head) (by simpa only [← same] using derives)

/-- Soundness requires justification for every CFG production, not merely
coverage of the intended source alternatives. -/
theorem Witness.production_yields {w : Witness} (checked : w.Conditions source p)
    (member : production ∈ p.grammar.productions)
    (yield : Yields source p w.meanings production.output word) :
    AtomYields source p w.meanings (.nonterminal production.input) word := by
  rcases checked with ⟨_, _, _, _, _, _, rules, exactRules⟩
  rw [exactRules] at member
  obtain ⟨rule, ruleMember, same⟩ := Array.mem_map.mp member
  subst production
  exact rule.yields (rules rule ruleMember) yield

/-- One arbitrary contextual rewrite can be interpreted backwards. -/
theorem Witness.produces_yields {w : Witness} (checked : w.Conditions source p)
    (step : p.grammar.semantics.Produces before after)
    (yield : Yields source p w.meanings after word) :
    Yields source p w.meanings before word := by
  obtain ⟨production, member, rewrite⟩ := step
  obtain ⟨pre, post, rfl, rfl⟩ := rewrite.exists_parts
  have member : production ∈ p.grammar.productions := by
    change production ∈ p.grammar.productions.toList.toFinset at member
    simpa using (List.mem_toFinset (l := p.grammar.productions.toList)).mp member
  obtain ⟨front, back, rfl, frontYield, backYield⟩ := Yields.append_iff.mp yield
  obtain ⟨left, middle, rfl, leftYield, middleYield⟩ := Yields.append_iff.mp frontYield
  exact (leftYield.append (Yields.singleton_iff.mpr
    (w.production_yields checked member middleYield))).append backYield

/-- Interpretation reflects any finite CFG derivation, including recursive
and nullable grammars. -/
theorem Witness.derives_yields {w : Witness} (checked : w.Conditions source p)
    (derivation : p.grammar.semantics.Derives before after)
    (yield : Yields source p w.meanings after word) :
    Yields source p w.meanings before word := by
  induction derivation using Relation.ReflTransGen.head_induction_on with
  | refl => exact yield
  | head step _ ih => exact w.produces_yields checked step ih

theorem Yields.terminals (word : List Nat) :
    Yields source p meanings (word.map _root_.Symbol.terminal) (word.map p.decode) := by
  induction word with
  | nil => exact .nil
  | cons token tokens ih =>
    exact .cons (symbol := .terminal token) (word := [p.decode token]) rfl ih

/-- Acceptance by the lowered CFG implies independent EBNF membership of
its decoded word. Encoding reflection supplies the converse boundary later. -/
theorem Witness.accepts_decoded {w : Witness} (checked : w.Conditions source p)
    (accepted : p.grammar.Accepts word) : EBNF.Accepts source (word.map p.decode) := by
  have interpreted := w.derives_yields checked accepted (Yields.terminals word)
  have initial := Yields.singleton_iff.mp interpreted
  rcases checked with ⟨nonempty, start, _, _, _, roots, _, _⟩
  cases source with
  | nil => exact False.elim (nonempty rfl)
  | cons rule tail =>
    rcases rule with ⟨name, body⟩
    refine ⟨name, body, tail, rfl, ?_⟩
    have initialMeaning := (roots ⟨0, by simp⟩).1
    obtain ⟨expr, lookup, derives⟩ := initial
    change w.meanings[p.grammar.start]? = some expr at lookup
    rw [start, initialMeaning] at lookup
    obtain rfl := Option.some.inj lookup
    exact derives

end Parser.LALR.Frontend
