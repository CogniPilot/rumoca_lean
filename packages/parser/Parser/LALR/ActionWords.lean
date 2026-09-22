import Parser.LALR.EBNFActions

/-! Generic, independent token-yield semantics for typed structural actions.
This is an inductive proof relation, not an executable recognizer. References
delegate through the same typed rule table; no finite expansion, structural
tree or run appears in the relation's definition. -/
namespace Parser.LALR.Frontend.StructuralActions

inductive Words (rules : Rules Payload Result) (classify : Payload → Parser.Symbol) :
    {α : Type} → Action Payload Result α → List Payload → α → Prop where
  | empty : Words rules classify .empty [] ()
  | terminal (same : classify payload = symbol) :
      Words rules classify (.terminal symbol) [payload] payload
  | seq : Words rules classify a left x → Words rules classify b right y →
      Words rules classify (.seq a b) (left ++ right) (x, y)
  | altLeft : Words rules classify a word result →
      Words rules classify (.alt a b) word result
  | altRight : Words rules classify b word result →
      Words rules classify (.alt a b) word result
  | ref (found : rules name = some rule) : Words rules classify rule word result →
      Words rules classify (.ref name) word result
  | map : Words rules classify a word result →
      Words rules classify (.map f a) word (f result)
  | optionalEmpty : Words rules classify (.optional a) [] none
  | optionalSome : Words rules classify a word result →
      Words rules classify (.optional a) word (some result)
  | manyEmpty : Words rules classify (.many a) [] []
  | manyCons : Words rules classify a head first → Words rules classify (.many a) tail rest →
      Words rules classify (.many a) (head ++ tail) (first :: rest)

theorem denotes_words (h : Denotes rules classify a v result) :
    Words rules classify a v.tokens result := by
  induction h with
  | empty => exact .empty
  | terminal same => exact .terminal same
  | seq _ _ ih ih' => exact .seq ih ih'
  | altLeft _ ih => exact .altLeft ih
  | altRight _ ih => exact .altRight ih
  | ref found _ ih => exact .ref found ih
  | map _ ih => exact .map ih
  | optionalEmpty => exact .optionalEmpty
  | optionalSome _ ih => exact .optionalSome ih
  | manyEmpty => exact .manyEmpty
  | manyCons _ _ ih ih' => exact .manyCons ih ih'

namespace Words
variable {rules : Rules Payload Result} {classify : Payload → Parser.Symbol}

/-- One-layer inversion view. This definition is nonrecursive: children and
named rule bodies refer back to the inductive Words relation. In particular it
does not expand a reference into a finite action program. -/
def Step (rules : Rules Payload Result) (classify : Payload → Parser.Symbol) :
    {α : Type} → Action Payload Result α → List Payload → α → Prop
  | _, .empty, word, _ => word = []
  | _, .terminal symbol, word, result => word = [result] ∧ classify result = symbol
  | _, .seq a b, word, result => ∃ left right,
      Words rules classify a left result.1 ∧ Words rules classify b right result.2 ∧
        word = left ++ right
  | _, .alt a b, word, result =>
      Words rules classify a word result ∨ Words rules classify b word result
  | _, .ref name, word, result =>
      ∃ rule, rules name = some rule ∧ Words rules classify rule word result
  | _, .map f a, word, result => ∃ x, f x = result ∧ Words rules classify a word x
  | _, .optional a, word, result => (word = [] ∧ result = none) ∨
      ∃ x, result = some x ∧ Words rules classify a word x
  | _, .many a, word, result => (word = [] ∧ result = []) ∨
      ∃ x xs left right, result = x :: xs ∧ word = left ++ right ∧
        Words rules classify a left x ∧ Words rules classify (.many a) right xs

theorem step_iff {a : Action Payload Result α} :
    Words rules classify a word result ↔ Step rules classify a word result := by
  constructor
  · intro h
    induction h with
    | empty => rfl
    | terminal same => exact ⟨rfl, same⟩
    | seq left right _ _ => exact ⟨_, _, left, right, rfl⟩
    | altLeft h _ => exact Or.inl h
    | altRight h _ => exact Or.inr h
    | ref found h _ => exact ⟨_, found, h⟩
    | map h _ => exact ⟨_, rfl, h⟩
    | optionalEmpty => exact Or.inl ⟨rfl, rfl⟩
    | optionalSome h _ => exact Or.inr ⟨_, rfl, h⟩
    | manyEmpty => exact Or.inl ⟨rfl, rfl⟩
    | manyCons h h' _ _ => exact Or.inr ⟨_, _, _, _, rfl, rfl, h, h'⟩
  · cases a with
    | empty => intro h; cases result; subst word; exact .empty
    | terminal s => rintro ⟨rfl, same⟩; exact .terminal same
    | seq a b =>
      cases result
      rintro ⟨left, right, hl, hr, rfl⟩
      exact .seq hl hr
    | alt a b =>
      rintro (h | h)
      · exact .altLeft h
      · exact .altRight h
    | ref name => rintro ⟨rule, found, body⟩; exact .ref found body
    | map f a => rintro ⟨x, rfl, body⟩; exact .map body
    | optional a =>
      rintro (⟨rfl, rfl⟩ | ⟨x, rfl, h⟩)
      · exact .optionalEmpty
      · exact .optionalSome h
    | many a =>
      rintro (⟨rfl, rfl⟩ | ⟨x, xs, left, right, rfl, rfl, hl, hr⟩)
      · exact .manyEmpty
      · exact .manyCons hl hr

theorem step (h : Words rules classify a word result) :
    Step rules classify a word result := step_iff.mp h

theorem empty_iff : Words rules classify .empty word result ↔ word = [] := by
  exact step_iff

theorem terminal_iff : Words rules classify (.terminal symbol) word result ↔
    word = [result] ∧ classify result = symbol := by
  exact step_iff

theorem seq_iff : Words rules classify (.seq a b) word result ↔
    ∃ left right, Words rules classify a left result.1 ∧
      Words rules classify b right result.2 ∧ word = left ++ right := by
  exact step_iff

theorem alt_iff : Words rules classify (.alt a b) word result ↔
    Words rules classify a word result ∨ Words rules classify b word result := by
  exact step_iff

theorem ref_iff (found : rules name = some rule) :
    Words rules classify (.ref name) word result ↔ Words rules classify rule word result := by
  constructor
  · intro h
    obtain ⟨other, found', body⟩ := step_iff.mp h
    cases Option.some.inj (found'.symm.trans found)
    exact body
  · exact .ref found

theorem map_iff : Words rules classify (.map f a) word result ↔
    ∃ x, f x = result ∧ Words rules classify a word x := by
  exact step_iff

theorem optional_iff : Words rules classify (.optional a) word result ↔
    (word = [] ∧ result = none) ∨
      ∃ x, result = some x ∧ Words rules classify a word x := by
  exact step_iff

theorem many_iff : Words rules classify (.many a) word result ↔
    (word = [] ∧ result = []) ∨
      ∃ x xs left right, result = x :: xs ∧ word = left ++ right ∧
        Words rules classify a left x ∧ Words rules classify (.many a) right xs := by
  exact step_iff

end Words
end Parser.LALR.Frontend.StructuralActions

