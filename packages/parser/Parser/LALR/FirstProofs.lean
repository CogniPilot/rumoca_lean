import Parser.LALR.First

/-! Checked FIRST information covers mathlib CFG derivations. These proofs
are independent of candidate table construction and parser execution. -/
namespace Parser.LALR.FirstProofs

def Nullable (facts : Array First) : List Atom → Prop
  | [] => True
  | .terminal _ :: _ => False
  | .nonterminal n :: rest => (facts[n]?.getD {}).nullable = true ∧ Nullable facts rest

def Begins (facts : Array First) (token : Nat) : List Atom → Prop
  | [] => False
  | .terminal t :: _ => token = t
  | .nonterminal n :: rest => token ∈ (facts[n]?.getD {}).terminals ∨
      (facts[n]?.getD {}).nullable = true ∧ Begins facts token rest

theorem mem_mergeTerminals : t ∈ mergeTerminals left right ↔ t ∈ left ∨ t ∈ right := by
  simp [mergeTerminals]

theorem sequence_nullable : (firstSequence facts symbols).nullable = true ↔
    Nullable facts symbols := by
  induction symbols with
  | nil => simp [firstSequence, Nullable]
  | cons symbol rest ih =>
    cases symbol with
    | terminal t => simp [firstSequence, Nullable]
    | nonterminal n =>
      cases h : (facts[n]?.getD {}).nullable <;> simp [firstSequence, Nullable, h, ih]

theorem sequence_begins : token ∈ (firstSequence facts symbols).terminals ↔
    Begins facts token symbols := by
  induction symbols with
  | nil => simp [firstSequence, Begins]
  | cons symbol rest ih =>
    cases symbol with
    | terminal t => simp [firstSequence, Begins]
    | nonterminal n =>
      cases h : (facts[n]?.getD {}).nullable <;>
        simp [firstSequence, Begins, h, mem_mergeTerminals, ih]

theorem nullable_append : Nullable facts (left ++ right) ↔
    Nullable facts left ∧ Nullable facts right := by
  induction left with
  | nil => simp [Nullable]
  | cons symbol rest ih =>
    cases symbol <;> simp [Nullable, ih, and_assoc]

theorem begins_append : Begins facts token (left ++ right) ↔
    Begins facts token left ∨ Nullable facts left ∧ Begins facts token right := by
  induction left with
  | nil => simp [Nullable, Begins]
  | cons symbol rest ih =>
    cases symbol with
    | terminal t => simp [Nullable, Begins]
    | nonterminal n => simp [Nullable, Begins, ih, and_or_left, or_assoc, and_assoc]

/-- Information ordering: every prediction on `a` is also present for `b`. -/
def Below (facts : Array First) (a b : List Atom) : Prop :=
  (Nullable facts a → Nullable facts b) ∧ ∀ token, Begins facts token a → Begins facts token b

theorem Below.refl : Below facts symbols symbols := ⟨id, fun _ => id⟩

theorem Below.trans (hab : Below facts a b) (hbc : Below facts b c) : Below facts a c :=
  ⟨fun h => hbc.1 (hab.1 h), fun t h => hbc.2 t (hab.2 t h)⟩

theorem Below.append_right (h : Below facts a b) (tail : List Atom) :
    Below facts (a ++ tail) (b ++ tail) := by
  constructor
  · rw [nullable_append, nullable_append]
    exact fun hn => ⟨h.1 hn.1, hn.2⟩
  · intro t
    rw [begins_append, begins_append]
    rintro (hb | ⟨hn, hb⟩)
    · exact Or.inl (h.2 t hb)
    · exact Or.inr ⟨h.1 hn, hb⟩

theorem Below.cons (h : Below facts a b) (symbol : Atom) :
    Below facts (symbol :: a) (symbol :: b) := by
  cases symbol with
  | terminal t => exact ⟨False.elim, fun _ => id⟩
  | nonterminal n =>
    constructor
    · exact fun hn => ⟨hn.1, h.1 hn.2⟩
    · intro t ht
      rcases ht with ht | ⟨hn, ht⟩
      · exact Or.inl ht
      · exact Or.inr ⟨hn, h.2 t ht⟩

theorem included_iff : FirstCheck.included a b = true ↔
    (a.nullable = true → b.nullable = true) ∧ ∀ t ∈ a.terminals, t ∈ b.terminals := by
  cases ha : a.nullable <;> cases hb : b.nullable <;>
    simp [FirstCheck.included, ha, hb, List.all_eq_true]

def Closed (g : Grammar) (facts : Array First) : Prop :=
  ∀ p ∈ g.productions.toList, Below facts p.output [.nonterminal p.input]

theorem validated_closed (h : FirstCheck.validate g facts = true) : Closed g facts := by
  simp only [FirstCheck.validate, Bool.and_eq_true] at h
  intro p hp
  have hc := Array.all_eq_true_iff_forall_mem.mp h.2 p (by simpa using hp)
  rw [included_iff] at hc
  constructor
  · intro hn
    exact ⟨hc.1 (sequence_nullable.mpr hn), trivial⟩
  · intro t ht
    exact Or.inl (hc.2 t (sequence_begins.mpr ht))

theorem rewrites_below (hc : Closed g facts) (hp : p ∈ g.productions.toList)
    (hr : p.Rewrites a b) : Below facts b a := by
  induction hr with
  | head tail => simpa using (hc p hp).append_right tail
  | cons symbol hr ih => exact ih.cons symbol

theorem produces_below (hc : Closed g facts) (h : g.semantics.Produces a b) :
    Below facts b a := by
  obtain ⟨p, hp, hr⟩ := h
  exact rewrites_below hc (List.mem_toFinset.mp hp) hr

theorem derives_below (hc : Closed g facts) (h : g.semantics.Derives a b) :
    Below facts b a := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact (produces_below hc hs).trans ih

/-- Any sequence that derives the empty word is marked nullable. This is a
coverage theorem, not a claim that every marked sequence can derive empty. -/
theorem nullable_complete (hc : FirstCheck.validate g facts = true)
    (h : g.semantics.Derives symbols []) :
    (firstSequence facts symbols).nullable = true :=
  sequence_nullable.mpr ((derives_below (validated_closed hc) h).1 trivial)

/-- Every terminal that can lead a derivation is in the checked FIRST summary. -/
theorem first_complete (hc : FirstCheck.validate g facts = true)
    (h : g.semantics.Derives symbols (.terminal token :: rest)) :
    token ∈ (firstSequence facts symbols).terminals :=
  sequence_begins.mpr ((derives_below (validated_closed hc) h).2 token rfl)

theorem mem_lookaheads : token ∈ lookaheads facts symbols following ↔
    Begins facts token symbols ∨ Nullable facts symbols ∧ token = following := by
  unfold lookaheads
  cases hn : (firstSequence facts symbols).nullable <;>
    simp [hn, mem_mergeTerminals, ← sequence_begins, ← sequence_nullable]

/-- The lookahead computation used in LR closure covers every derivable suffix,
including the caller's lookahead when that suffix is empty. -/
theorem lookahead_complete {word : List Nat} (hc : FirstCheck.validate g facts = true)
    (h : g.semantics.Derives symbols (word.map _root_.Symbol.terminal)) :
    word.headD following ∈ lookaheads facts symbols following := by
  apply mem_lookaheads.mpr
  cases word with
  | nil => exact Or.inr ⟨sequence_nullable.mp (nullable_complete hc h), rfl⟩
  | cons t tail => exact Or.inl (sequence_begins.mp (first_complete hc h))

end Parser.LALR.FirstProofs
