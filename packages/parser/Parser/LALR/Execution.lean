import Parser.LALR.Runtime

/-! Counted execution facts for derivation-directed LR completeness. These
relations describe the existing interpreter, not a second parser. Keeping the
step count explicit lets the completeness proof justify its eventual fuel. -/
namespace Parser.LALR.Execution

variable {g : Grammar} {tables : Tables}

inductive Steps (g : Grammar) (tables : Tables) : Nat → Configuration → Configuration → Prop
  | refl (c : Configuration) : Steps g tables 0 c c
  | next (hs : step g tables c = .next d) (rest : Steps g tables n d e) :
      Steps g tables (n + 1) c e

theorem Steps.trans (left : Steps g tables n a b) (right : Steps g tables m b c) :
    Steps g tables (n + m) a c := by
  induction left with
  | refl => simpa using right
  | next hs rest ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (Steps.next hs (ih right))

theorem Steps.run (steps : Steps g tables n a b) (fuel : Nat) :
    LALR.run g tables (n + fuel) a = LALR.run g tables fuel b := by
  induction steps with
  | refl => simp
  | next hs rest ih =>
    rw [Nat.add_right_comm, LALR.run, hs]
    exact ih

/-- Recover the actual row entry from the public table accessor. -/
theorem action_row (action : tables.action q token = some selected) :
    ∃ row, tables.actions[q]? = some row ∧ row[token]? = some (some selected) := by
  cases hr : tables.actions[q]? with
  | none => simp [Tables.action, hr] at action
  | some row =>
    cases he : row[token]? with
    | none => simp [Tables.action, hr, he] at action
    | some entry =>
      have same : entry = some selected := by simpa [Tables.action, hr, he] using action
      exact ⟨row, rfl, same ▸ he⟩

theorem shift (stack : List Frame) (token : Nat) (rest : List Nat) (target : Nat)
    (token_valid : token < g.terminals) (target_valid : target < tables.actions.size)
    (action : tables.action (Configuration.state ⟨stack, token :: rest⟩) token =
      some (.shift target)) :
    step g tables ⟨stack, token :: rest⟩ =
      .next ⟨⟨target, .terminal token⟩ :: stack, rest⟩ := by
  obtain ⟨row, hr, he⟩ := action_row action
  simp [step, Nat.not_le_of_gt token_valid, Nat.not_le_of_gt target_valid, hr, he]

theorem reduce (frames stack : List Frame) (input : List Nat)
    (index target : Nat) (p : Production)
    (input_valid : input = [] ∨ input.headD g.terminals < g.terminals)
    (rule : g.productions[index]? = some p)
    (count : frames.length = p.output.length)
    (symbols : p.output = (frames.reverse.map Frame.tree).map Tree.symbol)
    (action : tables.action (Configuration.state ⟨frames ++ stack, input⟩)
      (input.headD g.terminals) = some (.reduce index))
    (goto : tables.goto (Configuration.state ⟨stack, input⟩) p.input = some target)
    (target_valid : target < tables.actions.size) :
    step g tables ⟨frames ++ stack, input⟩ =
      .next ⟨⟨target, .node index p.input (frames.reverse.map Frame.tree)⟩ :: stack, input⟩ := by
  obtain ⟨row, hr, he⟩ := action_row action
  have valid : (!input.isEmpty && decide (input.headD g.terminals ≥ g.terminals)) = false := by
    rcases input_valid with rfl | bound
    · simp
    · have bad : decide (input.headD g.terminals ≥ g.terminals) = false := by
        simp only [decide_eq_false_iff_not]
        exact Nat.not_le_of_gt bound
      rw [bad, Bool.and_false]
  have split : (frames ++ stack).splitAt p.output.length = (frames, stack) := by
    rw [← count, List.splitAt_eq]
    simp
  simp only [step, Id.run, bind, pure, valid, Bool.false_eq_true, ↓reduceIte,
    hr, he, rule, split]
  simp only [count, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  simp only [symbols, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  have hg : tables.goto (((stack.head?).map Frame.state).getD 0) p.input = some target := goto
  rw [hg]
  simp only [Nat.not_le_of_gt target_valid, ↓reduceIte]

theorem accept (tree : Tree) (q : Nat)
    (start : tree.symbol = .nonterminal g.start)
    (action : tables.action q g.terminals = some .accept) :
    step g tables ⟨[⟨q, tree⟩], []⟩ = .accepted tree := by
  obtain ⟨row, hr, he⟩ := action_row action
  simp [step, Configuration.state, hr, he, start]

end Parser.LALR.Execution
