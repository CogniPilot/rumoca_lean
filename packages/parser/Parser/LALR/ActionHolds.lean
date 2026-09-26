import Parser.LALR.EBNFActions

/-! Invariants of typed structural actions. `Action.Holds` states that every
constituent a result is built from satisfies its rule's invariant, and every
retained payload has the class of its terminal. A rule table establishes an
invariant family when each rule body's constituents imply the invariant of the
rule result; then every result the actions denote satisfies it. The relation is
checked once per action body, as coverage and printing are. -/
namespace Parser.LALR.Frontend.StructuralActions

variable {Payload : Type} {Result : String → Type}

/-- `a.Holds classify good x`: `x` is built by `a` from constituents that
satisfy their invariants. -/
def Action.Holds (classify : Payload → Parser.Symbol) (good : (name : String) → Result name → Prop) :
    {α : Type} → Action Payload Result α → α → Prop
  | _, .empty, _ => True
  | _, .terminal s, x => classify x = s
  | _, .seq a b, x => a.Holds classify good x.1 ∧ b.Holds classify good x.2
  | _, .alt a b, x => a.Holds classify good x ∨ b.Holds classify good x
  | _, .ref name, x => good name x
  | _, .map f a, y => ∃ x, f x = y ∧ a.Holds classify good x
  | _, .optional a, o => ∀ x ∈ o, a.Holds classify good x
  | _, .many a, xs => ∀ x ∈ xs, a.Holds classify good x

/-- Every rule body establishes the invariant of its rule name. -/
def Establishes (rules : Rules Payload Result) (classify : Payload → Parser.Symbol)
    (good : (name : String) → Result name → Prop) : Prop :=
  ∀ name rule, rules name = some rule → ∀ x, rule.Holds classify good x → good name x

/-- Every denoted result satisfies the invariant its action establishes. -/
theorem Denotes.holds {rules : Rules Payload Result} {classify : Payload → Parser.Symbol}
    {good : (name : String) → Result name → Prop} (establishes : Establishes rules classify good)
    {α : Type} {a : Action Payload Result α} {v : Structure.Value Payload} {result : α}
    (h : Denotes rules classify a v result) : a.Holds classify good result := by
  induction h with
  | empty => trivial
  | terminal same => exact same
  | seq _ _ left right => exact ⟨left, right⟩
  | altLeft _ ih => exact .inl ih
  | altRight _ ih => exact .inr ih
  | ref found _ ih => exact establishes _ _ found _ ih
  | map _ ih => exact ⟨_, rfl, ih⟩
  | optionalEmpty => intro _ member; cases member
  | optionalSome _ ih => intro _ member; cases member; exact ih
  | manyEmpty => intro _ member; cases member
  | manyCons _ _ head tail =>
    intro x member
    rcases List.mem_cons.mp member with same | later
    · subst same; exact head
    · exact tail x later

end Parser.LALR.Frontend.StructuralActions
