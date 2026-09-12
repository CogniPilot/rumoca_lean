import Parser.LALR.EBNFWitness

/-! Every independent EBNF derivation is simulated by the actual CFG when
its finite structural witness passes. Induction is on source derivations, so
recursive references do not require acyclic expansion or bounded unrolling. -/
namespace Parser.LALR.Frontend

variable {source : EBNF.Grammar} {p : Prepared} {w : Witness}
variable {g : Grammar} {production : Production}

private theorem rule_derives (member : production ∈ g.productions) :
    g.semantics.Derives [.nonterminal production.input] production.output := by
  have step : g.semantics.Produces [.nonterminal production.input] production.output :=
    ⟨production, (List.mem_toFinset (l := g.productions.toList)).mpr (by simpa using member),
      ContextFreeRule.Rewrites.input_output⟩
  exact step.single

private theorem append_derives {a b : List Atom} {first second : List Nat}
    (left : g.semantics.Derives a (first.map _root_.Symbol.terminal))
    (right : g.semantics.Derives b (second.map _root_.Symbol.terminal)) :
    g.semantics.Derives (a ++ b) ((first ++ second).map _root_.Symbol.terminal) := by
  simpa only [List.map_append] using
    (left.append_right b).trans (right.append_left (first.map _root_.Symbol.terminal))

/-- A referenced rule slot resolves to the same body used by the source
semantics. This is a source-name lookup obligation, not a backend lookup. -/
theorem Witness.reference {n name body} (checked : w.Conditions source p)
    (slot : (source[n]?).map Prod.fst = some name) (rule : (name, body) ∈ source) :
    ∃ f : Fragment, f.expr = body ∧ f.Checked source p w.meanings ∧
      ContextFreeRule.mk n f.rhs ∈ p.grammar.productions := by
  obtain ⟨entry, lookup, sameName⟩ := Option.map_eq_some_iff.mp slot
  obtain ⟨bound, sameEntry⟩ := List.getElem?_eq_some_iff.mp lookup
  rcases checked with ⟨_, _, _, _, unique, roots, _, _⟩
  have sameBody := unique entry (List.mem_of_getElem? lookup) (name, body) rule sameName
  obtain ⟨f, _, expr, valid, member⟩ := (roots ⟨n, bound⟩).2
  refine ⟨f, ?_, valid, member⟩
  exact expr.trans ((congrArg Prod.snd sameEntry).trans sameBody)

/-- Coverage of every source case, universally over derivations and the
candidate representation of their expressions. -/
theorem Witness.fragment_complete (checked : w.Conditions source p)
    (derivation : EBNF.Derives source expr word) :
    ∀ f : Fragment, f.expr = expr → f.Checked source p w.meanings →
      p.grammar.semantics.Derives f.rhs ((word.map p.encode).map _root_.Symbol.terminal) := by
  induction derivation with
  | empty =>
    intro f same valid
    cases f <;> simp only [Fragment.expr, EBNF.Expr.terminal.injEq,
      reduceCtorEq] at same
    · exact .refl _
    · subst same
      exact False.elim (valid.1.2.2 rfl)
  | @terminal symbol nonempty =>
    intro f same valid
    cases f <;> simp only [Fragment.expr, EBNF.Expr.terminal.injEq,
      reduceCtorEq] at same
    · exact False.elim (nonempty same.symm)
    · rename_i actual code
      subst actual
      simpa only [Fragment.rhs, List.map_cons, List.map_nil, valid.1.2.1] using
        (ContextFreeGrammar.Derives.refl (g := p.grammar.semantics) [.terminal code])
  | @ref name body word rule _ ih =>
    intro f same valid
    cases f <;> simp only [Fragment.expr, EBNF.Expr.ref.injEq, reduceCtorEq] at same
    rename_i actual n
    subst actual
    obtain ⟨bodyFragment, bodyExpr, bodyValid, member⟩ := w.reference checked valid.2 rule
    exact (rule_derives member).trans (ih bodyFragment bodyExpr bodyValid)
  | @seq left right first second _ _ ihLeft ihRight =>
    intro f same valid
    cases f <;> simp only [Fragment.expr, EBNF.Expr.seq.injEq, reduceCtorEq] at same
    rename_i a b
    have left := ihLeft a same.1 valid.1
    have right := ihRight b same.2 valid.2
    simpa only [Fragment.rhs, List.map_append] using append_derives left right
  | @altLeft left right word _ ih =>
    intro f same valid
    cases f <;> simp only [Fragment.expr, EBNF.Expr.alt.injEq, reduceCtorEq] at same
    rename_i n a b
    exact (rule_derives valid.2.1.1).trans (ih a same.1 valid.2.2.1)
  | @altRight left right word _ ih =>
    intro f same valid
    cases f <;> simp only [Fragment.expr, EBNF.Expr.alt.injEq, reduceCtorEq] at same
    rename_i n a b
    exact (rule_derives valid.2.1.2).trans (ih b same.2 valid.2.2.2)
  | optionalEmpty =>
    intro f same valid
    cases f <;> simp only [Fragment.expr, EBNF.Expr.optional.injEq, reduceCtorEq] at same
    exact rule_derives valid.2.1.1
  | @optionalSome body word _ ih =>
    intro f same valid
    cases f <;> simp only [Fragment.expr, EBNF.Expr.optional.injEq, reduceCtorEq] at same
    rename_i n a
    exact (rule_derives valid.2.1.2).trans (ih a same valid.2.2)
  | manyEmpty =>
    intro f same valid
    cases f <;> simp only [Fragment.expr, EBNF.Expr.many.injEq, reduceCtorEq] at same
    exact rule_derives valid.2.1.1
  | @manyCons body first rest _ _ ihFirst ihRest =>
    intro f same valid
    cases f <;> simp only [Fragment.expr, EBNF.Expr.many.injEq, reduceCtorEq] at same
    rename_i n a
    have head := ihFirst a same valid.2.2
    have tail := ihRest (.many n a) (congrArg EBNF.Expr.many same) valid
    have combined := append_derives head tail
    simpa only [Fragment.rhs, List.map_append] using
      (rule_derives valid.2.1.2).trans combined

/-- Completeness for the actual start rule of every certified EBNF lowering. -/
theorem Witness.accepts_encoded (checked : w.Conditions source p)
    (accepted : EBNF.Accepts source word) : p.grammar.Accepts (word.map p.encode) := by
  obtain ⟨name, body, tail, rfl, derivation⟩ := accepted
  have root : Fragment.Checked ((name, body) :: tail) p w.meanings (.ref name 0) :=
    ⟨(checked.2.2.2.2.2.1 ⟨0, by simp⟩).1, rfl⟩
  have complete := w.fragment_complete checked derivation (.ref name 0) rfl root
  change p.grammar.semantics.Derives [.nonterminal p.grammar.start] _
  rw [checked.2.1]
  exact complete

end Parser.LALR.Frontend
