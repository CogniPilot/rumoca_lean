import Parser.LALR.Safety

/-! Bitmask reformulation of the structural-safety pop computation.

The reduction and acceptance summaries in `Safety.popStates` are vectors over
the automaton's states. Representing each such vector as a `Nat` bitmask lets the
kernel fold over the edge and goto lists once with machine-word bit operations
instead of re-expanding an `Array.ofFn` at every symbol. The results here are
purely equational: every masked computation is proved equal to the array
computation it replaces, so the certificates keep their original statements. -/
namespace Parser.LALR.Safety

/-- `testBit` of a single set bit. -/
theorem testBit_shiftOne (t q : Nat) : ((1 <<< t : Nat)).testBit q = decide (t = q) := by
  rw [show (1 <<< t : Nat) = 2 ^ t from by rw [Nat.shiftLeft_eq, one_mul], Nat.testBit_two_pow]

/-- A shift edge is honoured when it carries the reduction symbol and its source
is already reachable in the successor mask. -/
def goodEdge (symbol : Atom) (next : Nat) (e : Edge) : Bool :=
  (e.symbol == symbol) && next.testBit e.source

/-- Targets that must be excluded because some incoming edge is not honoured. -/
def badMask (edges : List Edge) (symbol : Atom) (next : Nat) : Nat :=
  edges.foldl (fun acc e => if goodEdge symbol next e then acc else acc ||| (1 <<< e.target)) 0

theorem badMask_char (edges : List Edge) (symbol : Atom) (next : Nat) (q : Nat) :
    (badMask edges symbol next).testBit q =
      edges.any (fun e => !goodEdge symbol next e && decide (e.target = q)) := by
  unfold badMask
  suffices h : ∀ acc : Nat, (edges.foldl (fun acc e => if goodEdge symbol next e then acc else acc ||| (1 <<< e.target)) acc).testBit q =
      (acc.testBit q || edges.any (fun e => !goodEdge symbol next e && decide (e.target = q))) by
    simpa using h 0
  intro acc
  induction edges generalizing acc with
  | nil => simp
  | cons e rest ih =>
    simp only [List.foldl_cons, List.any_cons]
    rw [ih]
    by_cases hg : goodEdge symbol next e
    · simp [hg]
    · rw [if_neg (by simpa using hg)]
      rw [Nat.testBit_or, testBit_shiftOne]
      simp only [hg, Bool.not_false, Bool.true_and]
      by_cases ht : e.target = q <;> simp [ht, Bool.or_comm]

/-- Bitmask of the set positions in a boolean state vector, bounded by `count`. -/
def arrayToMask (count : Nat) (a : Array Bool) : Nat :=
  (List.range count).foldl (fun acc q => if a[q]?.getD false then acc ||| (1 <<< q) else acc) 0

theorem arrayToMask_char (count : Nat) (a : Array Bool) (q : Nat) :
    (arrayToMask count a).testBit q = (decide (q < count) && (a[q]?.getD false)) := by
  unfold arrayToMask
  suffices h : ∀ acc : Nat, ∀ lo : Nat, (((List.range' lo count).foldl (fun acc q => if a[q]?.getD false then acc ||| (1 <<< q) else acc) acc)).testBit q =
      (acc.testBit q || (decide (lo ≤ q ∧ q < lo + count) && (a[q]?.getD false))) by
    have := h 0 0
    simp only [List.range_eq_range', Nat.zero_add] at this ⊢
    rw [this]; simp
  intro acc lo
  induction count generalizing acc lo with
  | zero => simp
  | succ n ih =>
    rw [List.range'_succ, List.foldl_cons, ih _ (lo+1)]
    by_cases hlo : a[lo]?.getD false = true
    · rw [if_pos hlo, Nat.testBit_or, testBit_shiftOne]
      by_cases hq : q = lo
      · subst hq
        rw [show decide (q + 1 ≤ q ∧ q < q + 1 + n) = false from by rw [decide_eq_false_iff_not]; omega,
            show decide (q ≤ q ∧ q < q + (n+1)) = true from by rw [decide_eq_true_eq]; omega]
        simp [hlo]
      · have hne : lo ≠ q := fun h => hq h.symm
        have e1 : (lo + 1 ≤ q ∧ q < lo + 1 + n) ↔ (lo ≤ q ∧ q < lo + (n+1)) := by omega
        simp only [hne, decide_false, Bool.or_false]
        rw [decide_eq_decide.mpr e1]
    · rw [if_neg hlo]
      by_cases hq : q = lo
      · subst hq
        simp only [Bool.not_eq_true] at hlo
        rw [show decide (q ≤ q ∧ q < q + (n+1)) = true from by rw [decide_eq_true_eq]; omega]
        simp [hlo]
      · have e1 : (lo + 1 ≤ q ∧ q < lo + 1 + n) ↔ (lo ≤ q ∧ q < lo + (n+1)) := by omega
        rw [decide_eq_decide.mpr e1]

/-- All state positions except the exclusive stack bottom (state zero). -/
def allButZero (count : Nat) : Nat := 2 ^ count - 2

/-- One backward pop step over the mask: keep every non-bottom target none of
whose incoming edges are dishonoured. -/
def stepMask (count : Nat) (edges : List Edge) (symbol : Atom) (next : Nat) : Nat :=
  allButZero count &&& ((2 ^ count - 1) ^^^ badMask edges symbol next)

/-- The full masked pop, folding the reduction symbols top-first. -/
def popMask (count : Nat) (edges : List Edge) : List Atom → Nat → Nat
  | [], base => base
  | s :: rest, base => stepMask count edges s (popMask count edges rest base)

/-- Expand a mask back into a boolean state vector of length `count`. -/
def maskToArray (count : Nat) (m : Nat) : Array Bool := Array.ofFn (n := count) (fun q => m.testBit q.val)

theorem allButZero_char (count q : Nat) : (allButZero count).testBit q = decide (0 < q ∧ q < count) := by
  unfold allButZero
  rcases count with _ | c
  · simp
  · have hp : 1 ≤ 2 ^ c := Nat.one_le_two_pow
    have hrw : 2 ^ (c + 1) - 2 = (2 ^ c - 1) <<< 1 := by
      rw [Nat.shiftLeft_eq, pow_succ]
      simp only [pow_one]
      omega
    rw [hrw, Nat.testBit_shiftLeft]
    simp only [Nat.testBit_two_pow_sub_one]
    by_cases h : 1 ≤ q
    · rw [decide_eq_true h, Bool.true_and, decide_eq_decide]; omega
    · rw [decide_eq_false (by omega : ¬ (1 ≤ q)), Bool.false_and, eq_comm,
          decide_eq_false_iff_not]; omega

theorem stepMask_char (count : Nat) (edges : List Edge) (symbol : Atom) (next q : Nat) :
    (stepMask count edges symbol next).testBit q =
      (decide (0 < q ∧ q < count) && !(badMask edges symbol next).testBit q) := by
  unfold stepMask
  rw [Nat.testBit_and, allButZero_char, Nat.testBit_xor, Nat.testBit_two_pow_sub_one]
  by_cases h : q < count
  · rw [decide_eq_true h, Bool.true_xor]
  · rw [decide_eq_false (by omega : ¬ q < count),
        decide_eq_false (show ¬(0 < q ∧ q < count) by omega)]
    simp

theorem popStates_size {count : Nat} {edges : List Edge} {after : Array Bool}
    (hsize : after.size = count) (syms : List Atom) :
    (Safety.popStates count edges syms after).size = count := by
  induction syms with
  | nil => simpa [Safety.popStates] using hsize
  | cons s rest ih => simp [Safety.popStates, Array.size_ofFn]

theorem all_congr' {α} (l : List α) (p r : α → Bool) (h : ∀ x ∈ l, p x = r x) :
    l.all p = l.all r := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.all_cons, List.all_cons, h a (List.mem_cons_self ..),
        ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

theorem pop_char {count : Nat} {edges : List Edge} (hb : ∀ e ∈ edges, e.source < count)
    {after : Array Bool} (hsize : after.size = count) :
    ∀ (syms : List Atom) (q : Nat), q < count →
      (Safety.popStates count edges syms after)[q]?.getD false =
        (popMask count edges syms (arrayToMask count after)).testBit q := by
  intro syms
  induction syms with
  | nil =>
    intro q hq
    simp only [Safety.popStates, popMask]
    rw [arrayToMask_char]; simp [hq]
  | cons s rest ih =>
    intro q hq
    have lhs : (Safety.popStates count edges (s :: rest) after)[q]?.getD false =
        ((q != 0) && edges.all (fun e => (e.target != q) ||
          (decide (e.symbol = s) && (Safety.popStates count edges rest after)[e.source]?.getD false))) := by
      simp only [Safety.popStates]
      rw [Array.getElem?_ofFn]; simp [hq]
    rw [lhs, popMask, stepMask_char, badMask_char, List.not_any_eq_all_not]
    rw [show (q != 0) = decide (0 < q) from by
          rw [show (q != 0) = decide (q ≠ 0) from by simp [bne, Bool.beq_eq_decide_eq]]
          rw [decide_eq_decide]; omega]
    rw [show decide (0 < q ∧ q < count) = decide (0 < q) from by rw [decide_eq_decide]; omega]
    congr 1
    apply all_congr'
    intro e he
    rw [ih e.source (hb e he)]
    simp only [goodEdge, Bool.not_and, Bool.not_or, Bool.not_not,
      show (e.target != q) = !decide (e.target = q) from by simp [bne, Bool.beq_eq_decide_eq],
      Bool.beq_eq_decide_eq]
    rw [Bool.or_comm]

/-- The array pop equals the masked pop expanded back into a vector. The edge
source bound and the input size are the same premises the safety validator
establishes for the table. -/
theorem popStates_eq {count : Nat} {edges : List Edge} (hb : ∀ e ∈ edges, e.source < count)
    {after : Array Bool} (hsize : after.size = count) (syms : List Atom) :
    Safety.popStates count edges syms after =
      maskToArray count (popMask count edges syms (arrayToMask count after)) := by
  apply Array.ext
  · rw [popStates_size hsize, maskToArray, Array.size_ofFn]
  · intro q h1 _
    have hqc : q < count := by rw [popStates_size hsize] at h1; exact h1
    have hpc := pop_char hb hsize syms q hqc
    rw [Array.getElem?_eq_getElem (by rw [popStates_size hsize]; exact hqc),
        Option.getD_some] at hpc
    rw [hpc]; simp only [maskToArray, Array.getElem_ofFn]

/-! ### Goto masks

`gotoStates` is itself an `Array.ofFn` over the states, so `arrayToMask` over it
would re-run a goto lookup for every state. Instead fold the goto table's rows
once, in order, tracking the row index. -/

/-- Fold a list of goto rows into a bitmask, setting bit `idx` when row `idx`
carries a goto on nonterminal `n`. -/
def rowsToMask (n : Nat) : List (Array (Option Nat)) → Nat → Nat → Nat
  | [], _, acc => acc
  | row :: rest, idx, acc =>
    rowsToMask n rest (idx + 1) (if (row[n]?.join).isSome then acc ||| (1 <<< idx) else acc)

/-- The single-pass goto mask: bit `q` is set exactly when `tables.goto q n` is
present. -/
def gotoMask (tables : Tables) (n : Nat) : Nat := rowsToMask n tables.gotos.toList 0 0

/-- Predicate on a goto row: it carries a goto on nonterminal `n`. -/
def rowHasGoto (n : Nat) (row : Array (Option Nat)) : Bool := (row[n]?.join).isSome

theorem rowsToMask_char (n q : Nat) :
    ∀ (rows : List (Array (Option Nat))) (idx base : Nat),
      (rowsToMask n rows idx base).testBit q =
        (base.testBit q ||
          (decide (idx ≤ q) && (rows[q - idx]?.map (rowHasGoto n)).getD false)) := by
  intro rows
  induction rows with
  | nil => intro idx base; simp [rowsToMask]
  | cons row rest ih =>
    intro idx base
    rw [rowsToMask, ih]
    have hstep : (if (row[n]?.join).isSome then base ||| (1 <<< idx) else base).testBit q =
        (base.testBit q || ((row[n]?.join).isSome && decide (idx = q))) := by
      by_cases hr : (row[n]?.join).isSome
      · rw [if_pos hr, Nat.testBit_or, testBit_shiftOne, hr, Bool.true_and]
      · rw [if_neg hr]
        simp only [Bool.not_eq_true] at hr
        simp only [hr, Bool.false_and, Bool.or_false]
    rw [hstep]
    rcases Nat.lt_trichotomy q idx with h | h | h
    · have h1 : ¬ (idx ≤ q) := by omega
      have h2 : ¬ (idx + 1 ≤ q) := by omega
      have h3 : idx ≠ q := by omega
      simp [h1, h2, h3]
    · subst h
      have h2 : ¬ (q + 1 ≤ q) := by omega
      simp [h2, Nat.sub_self, rowHasGoto]
    · have h1 : idx ≤ q := by omega
      have h2 : idx + 1 ≤ q := by omega
      have h3 : idx ≠ q := by omega
      have h4 : q - idx = (q - (idx + 1)) + 1 := by omega
      simp only [h1, h2, decide_true, Bool.true_and, h3, decide_false, Bool.and_false,
        Bool.or_false, h4, List.getElem?_cons_succ]

/-- The single-pass goto mask equals the bitmask of `gotoStates`. The goto table
has one row per state, the premise the safety validator already checks. -/
theorem gotoMask_eq {tables : Tables} {count : Nat}
    (hcount : tables.actions.size = count) (hg : tables.gotos.size = count) (n : Nat) :
    arrayToMask count (gotoStates tables n) = gotoMask tables n := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [arrayToMask_char, gotoMask, rowsToMask_char]
  simp only [Nat.zero_testBit, Bool.false_or, Nat.zero_le, decide_true, Bool.true_and,
    Nat.sub_zero]
  rw [gotoStates, Array.getElem?_ofFn]
  by_cases hq : q < count
  · have hqa : q < tables.actions.size := by rw [hcount]; exact hq
    have hqg : q < tables.gotos.toList.length := by rw [Array.length_toList, hg]; exact hq
    rw [dif_pos hqa]
    simp only [hq, decide_true, Bool.true_and, Option.getD_some,
      List.getElem?_eq_getElem hqg, Option.map_some, Option.getD_some, rowHasGoto,
      Array.getElem_toList]
    rw [Tables.goto]
    have hqg' : q < tables.gotos.size := by rw [hg]; exact hq
    rw [Array.getElem?_eq_getElem hqg']
    simp [Option.bind]
  · have hqa : ¬ q < tables.actions.size := by rw [hcount]; exact hq
    have hqg : ¬ q < tables.gotos.toList.length := by rw [Array.length_toList, hg]; exact hq
    rw [dif_neg hqa]
    simp only [hq, decide_false, Bool.false_and, Option.getD_none,
      List.getElem?_eq_none (Nat.le_of_not_lt hqg)]
    simp
end Parser.LALR.Safety
