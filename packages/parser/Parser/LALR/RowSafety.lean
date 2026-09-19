import Parser.LALR.Safety

/-! Per-row reformulation of the structural-safety table conditions.

`Safety.TableConditions` quantifies its action and goto obligations over every
state at once, so deciding the whole predicate builds a single kernel term
covering `states x symbols` cells and reaches a large transient peak.

This module isolates the obligations of one state into `rowValid`, keeping the
same array access as `entryOK`/`gotoOK` but reading only the row of that state.
`safety_of_rows` proves the whole-table conditions equivalent to the conjunction
of the per-state rows, letting a generator discharge one small kernel
certificate per state and join them, so the transient is bounded by a single row
rather than the whole table. Every statement is purely equational; the
validator's meaning is unchanged. -/
namespace Parser.LALR.Safety

/-- The whole-table action lookup equals reading the already-extracted action
row of state `q`. Holds unconditionally: an out-of-range state yields `none` on
both sides. -/
theorem action_eq_row (tables : Tables) (q a : Nat) :
    ((row tables q)[a]?).join = tables.action q a := by
  simp only [Tables.action, row]
  cases h : tables.actions[q]? with
  | none => simp
  | some r => simp

/-- The whole-table goto lookup equals reading the already-extracted goto row of
state `q`. -/
theorem goto_eq_row (tables : Tables) (q n : Nat) :
    ((gotoRow tables q)[n]?).join = tables.goto q n := by
  simp only [Tables.goto, gotoRow]
  cases h : tables.gotos[q]? with
  | none => simp
  | some r => simp

/-- Action-cell obligation for one already-extracted row `arow = row tables q`.
Identical to `entryOK` up to reading the row directly, which avoids re-indexing
the whole action table for every cell. -/
def entryRowOK (g : Grammar) (edges : List Edge)
    (reductions : Array (Array Bool)) (acceptance : Array Bool)
    (arow : Array (Option Action)) (q lookahead : Nat) : Prop :=
  match (arow[lookahead]?).join with
  | none => True
  | some (.shift target) => lookahead < g.terminals ∧ ⟨q, .terminal lookahead, target⟩ ∈ edges
  | some (.reduce index) =>
    match g.productions[index]? with
    | none => False
    | some _ => ((reductions[index]?.getD #[])[q]?).getD false = true
  | some .accept => lookahead = g.terminals ∧ (acceptance[q]?).getD false = true

instance : Decidable (entryRowOK g edges reductions acceptance arow q lookahead) := by
  unfold entryRowOK
  split <;> try infer_instance
  split <;> infer_instance

/-- Goto-cell obligation for one already-extracted goto row `grow = gotoRow
tables q`. Identical to `gotoOK` up to reading the row directly. -/
def gotoRowOK (edges : List Edge) (grow : Array (Option Nat)) (q n : Nat) : Prop :=
  match (grow[n]?).join with
  | none => True
  | some target => ⟨q, .nonterminal n, target⟩ ∈ edges

instance : Decidable (gotoRowOK edges grow q n) := by
  unfold gotoRowOK
  split <;> infer_instance

/-- Per-state structural validity: the action and goto rows of state `q` have the
required widths and every cell is honoured. The rows are extracted once, so a
single certificate touches only this state's row. -/
def rowValid (g : Grammar) (tables : Tables) (edges : List Edge)
    (reductions : Array (Array Bool)) (acceptance : Array Bool) (q : Nat) : Prop :=
  (row tables q).size = g.terminals + 1 ∧ (gotoRow tables q).size = g.nonterminals ∧
  (∀ a : Fin (g.terminals + 1), entryRowOK g edges reductions acceptance (row tables q) q a.val) ∧
  (∀ n : Fin g.nonterminals, gotoRowOK edges (gotoRow tables q) q n.val)

instance : Decidable (rowValid g tables edges reductions acceptance q) := by
  unfold rowValid; infer_instance

/-- The per-cell row action obligation matches the whole-table `entryOK`. -/
theorem entryRowOK_iff (g : Grammar) (tables : Tables) (edges : List Edge)
    (reductions : Array (Array Bool)) (acceptance : Array Bool) (q a : Nat) :
    entryRowOK g edges reductions acceptance (row tables q) q a
      ↔ entryOK g tables edges reductions acceptance q a := by
  unfold entryRowOK entryOK
  rw [action_eq_row]
  exact Iff.rfl

/-- The per-cell row goto obligation matches the whole-table `gotoOK`. -/
theorem gotoRowOK_iff (tables : Tables) (edges : List Edge) (q n : Nat) :
    gotoRowOK edges (gotoRow tables q) q n ↔ gotoOK tables edges q n := by
  unfold gotoRowOK gotoOK
  rw [goto_eq_row]
  exact Iff.rfl

/-- The whole-table conditions hold exactly when the four grammar/table prefix
conditions hold and every state's `rowValid` obligation holds. A generator can
discharge the right-hand side one state at a time, so no single kernel term
covers the whole table. -/
theorem safety_of_rows (g : Grammar) (tables : Tables) (edges : List Edge)
    (reductions : Array (Array Bool)) (acceptance : Array Bool)
    (hwf : g.wellFormed = true) (hsize : 0 < tables.actions.size)
    (hgsize : tables.gotos.size = tables.actions.size)
    (hedges : ∀ edge ∈ edges, edge.source < tables.actions.size ∧
      edge.target < tables.actions.size ∧ edge.target ≠ 0)
    (hrows : ∀ q : Fin tables.actions.size,
      rowValid g tables edges reductions acceptance q.val) :
    TableConditions g tables edges reductions acceptance := by
  refine ⟨hwf, hsize, hgsize, hedges, ?_, ?_, ?_⟩
  · intro q; exact ⟨(hrows q).1, (hrows q).2.1⟩
  · intro q a
    exact (entryRowOK_iff g tables edges reductions acceptance q.val a.val).mp ((hrows q).2.2.1 a)
  · intro q n
    exact (gotoRowOK_iff tables edges q.val n.val).mp ((hrows q).2.2.2 n)

end Parser.LALR.Safety
