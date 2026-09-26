import Parser.LALR.EBNFActions

/-! Payload preservation for typed structural actions. `Yields` states that a
printer recovers, from an action's result alone, the exact payload sequence of
every structural value the action denotes. A language whose rule table yields
its printer therefore has an AST that retains the complete token sequence of
the parsed text; no reparse, search or reconstruction from source positions is
involved. The relation is checked once per action body, as coverage is. -/
namespace Parser.LALR.Frontend.StructuralActions

variable {Payload : Type} {Result : String → Type}

/-- `a.Yields classify print p`: printing the result of `a` with `p` gives the
payloads of the denoted value. A terminal printer need only agree on payloads
of that terminal's class, so a result may omit fixed punctuation. -/
def Action.Yields (classify : Payload → Parser.Symbol)
    (print : (name : String) → Result name → List Payload) :
    {α : Type} → Action Payload Result α → (α → List Payload) → Prop
  | _, .empty, p => p () = []
  | _, .terminal s, p => ∀ x, classify x = s → p x = [x]
  | _, .seq a b, p => ∃ pa pb, a.Yields classify print pa ∧ b.Yields classify print pb ∧
      ∀ x y, p (x, y) = pa x ++ pb y
  | _, .alt a b, p => a.Yields classify print p ∧ b.Yields classify print p
  | _, .ref name, p => ∀ result, p result = print name result
  | _, .map f a, p => a.Yields classify print (fun x => p (f x))
  | _, .optional a, p => ∃ pa, a.Yields classify print pa ∧ ∀ o, p o = o.elim [] pa
  | _, .many a, p => ∃ pa, a.Yields classify print pa ∧ ∀ xs, p xs = xs.flatMap pa

/-- Every rule body yields the printer of its rule name. -/
def Yield (rules : Rules Payload Result) (classify : Payload → Parser.Symbol)
    (print : (name : String) → Result name → List Payload) : Prop :=
  ∀ name rule, rules name = some rule → rule.Yields classify print (print name)

variable {classify : Payload → Parser.Symbol} {print : (name : String) → Result name → List Payload}

/-- The payloads of every denoted value are the printed result. -/
theorem Denotes.tokens {rules : Rules Payload Result} (yield : Yield rules classify print)
    {α : Type} {a : Action Payload Result α} {v : Structure.Value Payload} {result : α}
    (h : Denotes rules classify a v result) {p : α → List Payload}
    (yields : a.Yields classify print p) : v.tokens = p result := by
  induction h with
  | empty => exact yields.symm
  | terminal same => exact (yields _ same).symm
  | seq _ _ left right =>
    obtain ⟨pa, pb, ha, hb, split⟩ := yields
    rw [split, Structure.Value.tokens, left ha, right hb]
  | altLeft _ ih => exact ih yields.1
  | altRight _ ih => exact ih yields.2
  | ref found _ ih =>
    rw [Structure.Value.tokens, ih (yield _ _ found), yields]
  | map _ ih => exact ih yields
  | optionalEmpty =>
    obtain ⟨_, _, printed⟩ := yields
    rw [printed]
    rfl
  | optionalSome _ ih =>
    obtain ⟨pa, ha, printed⟩ := yields
    rw [printed, Structure.Value.tokens, ih ha]
    rfl
  | manyEmpty =>
    obtain ⟨_, _, printed⟩ := yields
    rw [printed]
    rfl
  | manyCons _ _ head tail =>
    obtain ⟨pa, ha, printed⟩ := yields
    rw [printed, Structure.Value.tokens, head ha, tail ⟨pa, ha, printed⟩, printed, List.flatMap_cons]

theorem Action.Yields.terminal (s : Parser.Symbol) :
    (Action.terminal s : Action Payload Result Payload).Yields classify print (fun x => [x]) :=
  fun _ _ => rfl

/-- A terminal whose class admits one payload may be printed as that payload. -/
theorem Action.Yields.fixed {s : Parser.Symbol} {payload : Payload}
    (unique : ∀ x, classify x = s → x = payload) :
    (Action.terminal s : Action Payload Result Payload).Yields classify print (fun _ => [payload]) :=
  fun x same => by rw [unique x same]

theorem Action.Yields.ref (name : String) :
    (Action.ref name : Action Payload Result (Result name)).Yields classify print (print name) :=
  fun _ => rfl

theorem Action.Yields.seq {α β : Type} {a : Action Payload Result α} {b : Action Payload Result β}
    {pa : α → List Payload} {pb : β → List Payload}
    (left : a.Yields classify print pa) (right : b.Yields classify print pb) :
    (Action.seq a b).Yields classify print (fun xy => pa xy.1 ++ pb xy.2) :=
  ⟨pa, pb, left, right, fun _ _ => rfl⟩

theorem Action.Yields.alt {α : Type} {a b : Action Payload Result α} {p : α → List Payload}
    (left : a.Yields classify print p) (right : b.Yields classify print p) :
    (Action.alt a b).Yields classify print p :=
  ⟨left, right⟩

theorem Action.Yields.optional {α : Type} {a : Action Payload Result α} {pa : α → List Payload}
    (body : a.Yields classify print pa) :
    (Action.optional a).Yields classify print (fun o => o.elim [] pa) :=
  ⟨pa, body, fun _ => rfl⟩

theorem Action.Yields.many {α : Type} {a : Action Payload Result α} {pa : α → List Payload}
    (body : a.Yields classify print pa) :
    (Action.many a).Yields classify print (fun xs => xs.flatMap pa) :=
  ⟨pa, body, fun _ => rfl⟩

theorem Action.Yields.map {α β : Type} {a : Action Payload Result α} {f : α → β}
    {p : β → List Payload} (body : a.Yields classify print (fun x => p (f x))) :
    (Action.map f a).Yields classify print p :=
  body

/-- Printers that agree on every result are interchangeable. -/
theorem Action.Yields.congr {α : Type} {a : Action Payload Result α} {p q : α → List Payload}
    (yields : a.Yields classify print q) (same : ∀ x, p x = q x) :
    a.Yields classify print p := by
  induction a with
  | empty => exact (same ()).trans yields
  | terminal s => exact fun x c => (same x).trans (yields x c)
  | seq a b _ _ =>
    obtain ⟨pa, pb, ha, hb, split⟩ := yields
    exact ⟨pa, pb, ha, hb, fun x y => (same (x, y)).trans (split x y)⟩
  | alt a b iha ihb => exact ⟨iha yields.1 same, ihb yields.2 same⟩
  | ref name => exact fun r => (same r).trans (yields r)
  | map f a ih => exact ih yields (fun x => same (f x))
  | optional a _ =>
    obtain ⟨pa, ha, printed⟩ := yields
    exact ⟨pa, ha, fun o => (same o).trans (printed o)⟩
  | many a _ =>
    obtain ⟨pa, ha, printed⟩ := yields
    exact ⟨pa, ha, fun xs => (same xs).trans (printed xs)⟩

end Parser.LALR.Frontend.StructuralActions
