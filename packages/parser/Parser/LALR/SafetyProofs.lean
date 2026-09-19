import Parser.LALR.Safety
import Parser.LALR.MaskedSafety
import Parser.LALR.RuntimeProofs

/-! Structural safety of the actual shift/reduce interpreter. The concrete
stack invariant follows automaton edges; finite pop certificates cover every
such path, including recursive paths of unbounded stack depth. -/
namespace Parser.LALR.Safety

variable {g : Grammar} {tables : Tables} {edges : List Edge}
  {stack : List Frame} {c : Configuration} {p : Production} {index : Nat}

theorem pop_cons (hq : q < count)
    (h : ((popStates count edges (symbol :: rest) after)[q]?).getD false = true) :
    q ≠ 0 ∧ ∀ edge ∈ edges, edge.target = q →
      edge.symbol = symbol ∧ ((popStates count edges rest after)[edge.source]?).getD false = true := by
  rw [popStates] at h
  simp only [Array.getElem?_ofFn, hq, ↓reduceDIte, Option.getD_some,
    Bool.and_eq_true, bne_iff_ne, List.all_eq_true] at h
  refine ⟨h.1, ?_⟩
  intro edge he ht
  have h := h.2 edge he
  simpa [ht] using h

/-- A certified pop succeeds on every stack path, not just on sampled inputs. -/
theorem pop_sound (hc : Conditions g tables edges) (hp : Path edges stack)
    (h : ((popStates tables.actions.size edges symbols after)[state stack]?).getD false = true) :
    (stack.take symbols.length).length = symbols.length ∧
    (stack.take symbols.length).map (fun f => f.tree.symbol) = symbols ∧
    (after[state (stack.drop symbols.length)]?).getD false = true := by
  induction symbols generalizing stack with
  | nil => simpa only [popStates, List.length_nil, List.take_zero, List.map_nil,
      List.drop_zero, and_self, true_and] using h
  | cons symbol rest ih =>
    obtain ⟨hn, hall⟩ := pop_cons (path_state_lt hc hp) h
    cases stack with
    | nil => exact False.elim (hn rfl)
    | cons frame tail =>
      obtain ⟨hs, ht⟩ := hall _ hp.edge rfl
      change frame.tree.symbol = symbol at hs
      obtain ⟨hl, hr, ha⟩ := ih hp.tail ht
      simp only [List.length_cons, List.take_succ_cons, List.length_cons,
        List.map_cons, List.drop_succ_cons, hl, hs, hr, true_and]
      exact ha

theorem reduction_pop (hc : Conditions g tables edges) (hp : Path edges stack)
    (hprod : g.productions[index]? = some p)
    (h : (((reductionStates g tables edges)[index]?.getD #[])[state stack]?).getD false = true) :
    (stack.take p.output.length).length = p.output.length ∧
    (stack.take p.output.length).reverse.map (fun f => f.tree.symbol) = p.output ∧
    (tables.goto (state (stack.drop p.output.length)) p.input).isSome = true := by
  have hpop : ((popStates tables.actions.size edges p.output.reverse
      (gotoStates tables p.input))[state stack]?).getD false = true := by
    simpa only [reductionStates, Array.getElem?_map, hprod, Option.map_some,
      Option.getD_some] using h
  obtain ⟨hl, hs, ha⟩ := pop_sound hc hp hpop
  simp only [List.length_reverse] at hl hs ha
  refine ⟨hl, ?_, ?_⟩
  · rw [List.map_reverse, hs, List.reverse_reverse]
  · have hb := path_state_lt hc (hp.drop p.output.length)
    simpa [gotoStates, hb] using ha

theorem acceptance_stack (hc : Conditions g tables edges) (hp : Path edges stack)
    (h : ((acceptStates g tables edges)[state stack]?).getD false = true) :
    ∃ frame, stack = [frame] ∧ frame.tree.symbol = .nonterminal g.start := by
  obtain ⟨hl, hs, ha⟩ := pop_sound hc hp h
  have hb := path_state_lt hc (hp.drop 1)
  have hz : state (stack.drop 1) = 0 := by
    simpa only [List.length_singleton, Array.getElem?_ofFn, hb, ↓reduceDIte,
      Option.getD_some, beq_iff_eq] using ha
  have he := (path_state_zero hc (hp.drop 1)).mp hz
  cases stack with
  | nil => simp at hl
  | cons frame tail =>
    have ht : tail = [] := he
    subst tail
    refine ⟨frame, rfl, ?_⟩
    simpa using hs

theorem action_checked (hc : Conditions g tables edges)
    (hq : q < tables.actions.size) (ha : a < g.terminals + 1) :
    entryOK g tables edges (reductionStates g tables edges)
      (acceptStates g tables edges) q a :=
  hc.2.2.2.2.2.1 ⟨q, hq⟩ ⟨a, ha⟩

theorem goto_checked (hc : Conditions g tables edges)
    (hq : q < tables.actions.size) (hn : n < g.nonterminals)
    (he : tables.goto q n = some target) :
    ⟨q, .nonterminal n, target⟩ ∈ edges := by
  have h := hc.2.2.2.2.2.2 ⟨q, hq⟩ ⟨n, hn⟩
  simpa only [gotoOK, he] using h

theorem production_bound (hc : Conditions g tables edges)
    (he : g.productions[index]? = some p) : p.input < g.nonterminals := by
  have h := hc.1
  simp only [Grammar.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at h
  have h := Array.all_eq_true_iff_forall_mem.mp h.2 p (Array.mem_of_getElem? he)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

def OutcomeSafe (edges : List Edge) : StepResult → Prop
  | .next c => Path edges c.stack
  | .accepted _ => True
  | .failed e => e = .rejected

/-- Safety for one step of the actual interpreter, on every concrete stack
represented by the validator. Arbitrary unknown input tokens reject normally. -/
theorem step_safe (hc : Conditions g tables edges) (hp : Path edges c.stack) :
    OutcomeSafe edges (step g tables c) := by
  have hq : c.state < tables.actions.size := path_state_lt hc hp
  have hw := (hc.2.2.2.2.1 ⟨c.state, hq⟩).1
  change (row tables c.state).size = g.terminals + 1 at hw
  have hrow : tables.actions[c.state]? = some (row tables c.state) := by
    simp [row, hq]
  simp only [step, Id.run, bind, pure]
  split
  · rfl
  · rename_i goodInput
    rw [hrow]
    dsimp only
    have hlook : c.remaining.headD g.terminals < g.terminals + 1 := by
      cases hr : c.remaining with
      | nil => simp
      | cons token rest =>
        simp only [hr, List.isEmpty_cons, Bool.not_false, List.headD_cons,
          Bool.true_and, decide_eq_true_eq, not_le] at goodInput
        exact Nat.lt_succ_of_lt goodInput
    have hlookrow : c.remaining.headD g.terminals < (row tables c.state).size := by omega
    have hentry : (row tables c.state)[c.remaining.headD g.terminals]? =
        some ((row tables c.state)[c.remaining.headD g.terminals]) :=
      Array.getElem?_eq_getElem hlookrow
    rw [hentry]
    dsimp only
    have haction := action_checked hc hq hlook
    have ha : tables.action c.state (c.remaining.headD g.terminals) =
        (row tables c.state)[c.remaining.headD g.terminals] := by
      simp only [Tables.action, hrow, Option.bind_some, hentry, Option.join_some]
    cases he : (row tables c.state)[c.remaining.headD g.terminals] with
    | none => trivial
    | some action =>
      rw [entryOK, ha, he] at haction
      cases action with
      | shift target =>
        obtain ⟨hterminal, hedge⟩ := haction
        have ht := (hc.2.2.2.1 _ hedge).2.1
        change target < tables.actions.size at ht
        simp only [show ¬ target ≥ tables.actions.size by omega, ↓reduceIte]
        cases hr : c.remaining with
        | nil => simp [hr] at hterminal
        | cons token rest =>
          dsimp only
          apply Path.cons _ _ hp
          simpa only [hr, List.headD_cons, Tree.symbol] using hedge
      | reduce index =>
        cases heprod : g.productions[index]? with
        | none => simp only [heprod] at haction
        | some p =>
          dsimp only
          rw [heprod]
          simp only [heprod] at haction
          obtain ⟨hl, hs, hg⟩ := reduction_pop hc hp heprod haction
          have hgSome := Option.isSome_iff_exists.mp hg
          obtain ⟨target, htarget⟩ := hgSome
          have hrest := hp.drop p.output.length
          have hedge := goto_checked hc (path_state_lt hc hrest)
            (production_bound hc heprod) htarget
          have ht := (hc.2.2.2.1 _ hedge).2.1
          change target < tables.actions.size at ht
          simp only [List.splitAt_eq, hl, bne_self_eq_false, Bool.false_eq_true,
            ↓reduceIte, List.map_map, Function.comp_def]
          simp only [hs, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
          dsimp only [state] at htarget
          rw [htarget]
          simp only [show ¬ target ≥ tables.actions.size by omega, ↓reduceIte]
          exact Path.cons _ _ hrest hedge
      | accept =>
        obtain ⟨heof, hgood⟩ := haction
        obtain ⟨frame, hstack, hsymbol⟩ := acceptance_stack hc hp hgood
        cases hr : c.remaining with
        | cons token rest =>
          simp only [hr, List.headD_cons] at heof
          simp [hr, heof] at goodInput
        | nil =>
          simp [hstack, hsymbol, OutcomeSafe]

/-- Validated tables can only accept, reject a word, or exhaust fuel. They
cannot reach an internal table error at any finite point in an execution. -/
theorem run_safe (hc : Conditions g tables edges) (hp : Path edges c.stack)
    (h : run g tables fuel c = .error error) :
    error = .exhausted ∨ error = .rejected := by
  induction fuel generalizing c with
  | zero => cases Except.error.inj h; exact Or.inl rfl
  | succ fuel ih =>
    have hs := step_safe hc hp
    unfold run at h
    cases he : step g tables c with
    | next next =>
      rw [he] at h
      exact ih (by simpa only [he, OutcomeSafe] using hs) h
    | accepted tree => rw [he] at h; contradiction
    | failed reason =>
      rw [he] at h
      cases Except.error.inj h
      exact Or.inr (by simpa only [he, OutcomeSafe] using hs)

theorem validated_run_safe (hcheck : validate g tables edges = true)
    (h : run g tables fuel ⟨[], input⟩ = .error error) :
    error = .exhausted ∨ error = .rejected :=
  run_safe (validate_iff.mp hcheck) .nil h

/-- The public parser inherits table safety, and the execution word/tree
invariant rules out failure of its final certificate check as well. -/
theorem validated_parse_safe (hcheck : validate g tables edges = true)
    (h : parse g tables fuel input = .error error) :
    error = .exhausted ∨ error = .rejected := by
  unfold parse at h
  cases hr : run g tables fuel ⟨[], input⟩ with
  | error reason =>
    rw [hr] at h
    change Except.error reason = Except.error error at h
    cases Except.error.inj h
    exact validated_run_safe hcheck hr
  | ok tree =>
    have ht := RuntimeProofs.run_checked (RuntimeProofs.initial g input) hr
    rw [hr] at h
    change (if checkTree g input tree then Except.ok tree
      else Except.error Failure.invalidTree) = Except.error error at h
    rw [ht] at h
    contradiction

end Parser.LALR.Safety
