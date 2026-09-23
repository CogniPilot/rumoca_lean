import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

/-! Select exactly one occurrence of a key, not one distinct value. No equality
on list elements is required: two identical matching elements still reject.
The relation is independent of the executable and preserves the original item. -/
namespace Parser.UniqueSelection

universe u v
variable {Item : Type u} {Key : Type v}

def select [DecidableEq Key] (key : Item → Key) (wanted : Key) :
    List Item → Option Item
  | [] => none
  | item :: rest =>
      if key item = wanted then
        if ∀ other ∈ rest, key other ≠ wanted then some item else none
      else select key wanted rest

inductive Selects (key : Item → Key) (wanted : Key) : List Item → Item → Prop where
  | here (same : key item = wanted)
      (absent : ∀ other ∈ rest, key other ≠ wanted) :
      Selects key wanted (item :: rest) item
  | there (different : key head ≠ wanted) : Selects key wanted rest item →
      Selects key wanted (head :: rest) item

theorem Selects.mem (selected : Selects key wanted items item) : item ∈ items := by
  induction selected with
  | here => exact List.mem_cons_self
  | there _ _ ih => exact List.mem_cons_of_mem _ ih

theorem Selects.key_eq (selected : Selects key wanted items item) : key item = wanted := by
  induction selected with
  | here same _ => exact same
  | there _ _ ih => exact ih

theorem select_sound [DecidableEq Key] (key : Item → Key) (wanted : Key)
    (items : List Item) (item : Item) (found : select key wanted items = some item) :
    Selects key wanted items item := by
  induction items with
  | nil => simp [select] at found
  | cons head rest ih =>
    simp only [select] at found
    split at found
    · rename_i same
      split at found
      · rename_i absent
        cases Option.some.inj found
        exact .here same absent
      · contradiction
    · rename_i different
      exact .there different (ih found)

theorem select_complete [DecidableEq Key]
    (selected : Selects (Item := Item) (Key := Key) key wanted items item) :
    select key wanted items = some item := by
  induction selected with
  | here same absent => simp only [select, if_pos same, if_pos absent]
  | there different _ ih => simp only [select, if_neg different, ih]

theorem select_iff [DecidableEq Key] (key : Item → Key) (wanted : Key)
    (items : List Item) (item : Item) :
    select key wanted items = some item ↔ Selects key wanted items item :=
  ⟨select_sound key wanted items item, select_complete⟩

/-- Exact occurrence characterization: equality of matching values does not
collapse two positions into one. The filter appears only in this theorem. -/
theorem selects_iff_filter [DecidableEq Key] (key : Item → Key) (wanted : Key)
    (items : List Item) (item : Item) :
    Selects key wanted items item ↔
      items.filter (fun x => decide (key x = wanted)) = [item] := by
  induction items with
  | nil => constructor <;> intro h <;> cases h
  | cons head rest ih =>
    by_cases same : key head = wanted
    · simp only [List.filter_cons, same, decide_true, ite_true]
      constructor
      · intro selected
        cases selected with
        | here _ absent =>
          congr 1
          exact List.filter_eq_nil_iff.mpr (by simpa using absent)
        | there different _ => exact False.elim (different same)
      · intro equal
        obtain ⟨rfl, empty⟩ := List.cons.inj equal
        exact .here same (by simpa using List.filter_eq_nil_iff.mp empty)
    · simp only [List.filter_cons, same, decide_false, Bool.false_eq_true, ite_false]
      constructor
      · intro selected
        cases selected with
        | here equal _ => exact False.elim (same equal)
        | there _ selected => exact ih.mp selected
      · intro filtered
        exact .there same (ih.mpr filtered)

theorem selected_unique [DecidableEq Key]
    (first : Selects (Item := Item) (Key := Key) key wanted items a)
    (second : Selects key wanted items b) : a = b :=
  Option.some.inj ((select_complete first).symm.trans (select_complete second))

theorem select_none_iff [DecidableEq Key] (key : Item → Key) (wanted : Key)
    (items : List Item) :
    select key wanted items = none ↔ ¬ ∃ item, Selects key wanted items item := by
  cases found : select key wanted items with
  | none =>
    simp only [true_iff]
    rintro ⟨item, selected⟩
    have complete := select_complete selected
    rw [found] at complete
    contradiction
  | some item =>
    simp only [Option.some_ne_none, false_iff, not_not]
    exact ⟨item, (select_iff key wanted items item).mp found⟩

/-- Reject two matching occurrences anywhere, including `a = b` and arbitrary
unrelated or additional matching entries before, between and after them. -/
theorem select_repeated [DecidableEq Key] (key : Item → Key) (wanted : Key)
    (before between after : List Item) (a b : Item)
    (first : key a = wanted) (second : key b = wanted) :
    select key wanted (before ++ [a] ++ between ++ [b] ++ after) = none := by
  apply (select_none_iff key wanted _).mpr
  rintro ⟨item, selected⟩
  have filtered := (selects_iff_filter key wanted _ item).mp selected
  have lengths := congrArg List.length filtered
  simp only [List.filter_append, List.filter_cons, List.filter_nil,
    first, second, decide_true, ite_true, List.length_append,
    List.length_cons, List.length_nil] at lengths
  omega

end Parser.UniqueSelection
