import RumocaC.Body

namespace Rumoca.COutputAssignments
open CTree CMemory CBody

/-- A prepared C assignment through an output parameter. Source-language
resolution, shapes and solver choices have already been handled upstream. -/
structure Entry where
  name : String
  address : Address
  type : CType
  expression : Expr
  input : Value
  value : Value

def statement (entry : Entry) : Stmt := .assign (.deref (.id entry.name)) entry.expression

def write (heap : Heap) (entry : Entry) : Heap :=
  replace heap entry.address ⟨entry.type, true, some entry.value⟩

def after (heap : Heap) (entries : List Entry) : Heap := entries.foldl write heap

def Writable (heap : Heap) (entry : Entry) : Prop :=
  ∃ old, heap entry.address = some ⟨entry.type, true, old⟩

structure Ready [interface : CInterface] (env : Locals) (heap : Heap) (entry : Entry) : Prop where
  bound : resolve env entry.name = some (.pointer (some entry.address))
  expression : ∀ memory, eval env memory entry.expression = some entry.input
  nonatomic : entry.type ≠ .atomicBoolean
  conversion : convert entry.type entry.input = some entry.value
  writable : Writable heap entry

theorem write_frame (heap : Heap) (entry : Entry) (query : Address) (outside : query ≠ entry.address) :
    write heap entry query = heap query := replace_other _ _ _ _ outside

/-- Writes keep cell types, including when output parameters alias. -/
theorem writable_preserved (first : Writable heap entry) (other : Writable heap otherEntry) :
    Writable (write heap entry) otherEntry := by
  obtain ⟨old, first⟩ := first
  obtain ⟨previous, other⟩ := other
  by_cases same : otherEntry.address = entry.address
  · have types : otherEntry.type = entry.type := by
      rw [same] at other
      have equal := Option.some.inj (other.symm.trans first)
      exact congrArg Cell.type equal
    exact ⟨some entry.value, by simp [write, same, types]⟩
  · exact ⟨previous, (write_frame heap entry otherEntry.address same).trans other⟩

theorem ready_preserved [interface : CInterface] (first : Ready env heap entry) (other : Ready env heap otherEntry) :
    Ready env (write heap entry) otherEntry :=
  { other with writable := writable_preserved first.writable other.writable }

theorem run_one [interface : CInterface] (env : Locals) (heap : Heap) (entry : Entry)
    (rest : List Stmt) (ready : Ready env heap entry) :
    run 1 (.running (statement entry :: rest) env heap) =
      some (.running rest env (write heap entry)) := by
  obtain ⟨old, writable⟩ := ready.writable
  simp [run, next, nextWith, CBody.legacyExpressions, statement, eval, evalWith, lvalue, lvalueWith, ready.bound, ready.expression heap,
    Value.address, store, writable, ready.nonatomic, ready.conversion, write]

/-- Any prepared list executes through its exact successive heaps. No
target execution, distinct output addresses or initialized old values are assumed. -/
theorem run_all [interface : CInterface] (env : Locals) (heap : Heap) (entries : List Entry)
    (rest : List Stmt) (ready : ∀ entry ∈ entries, Ready env heap entry) :
    run entries.length (.running (entries.map statement ++ rest) env heap) =
      some (.running rest env (after heap entries)) := by
  induction entries generalizing heap with
  | nil => rfl
  | cons entry entries ih =>
    have head := ready entry (by simp)
    have tail : ∀ next ∈ entries, Ready env (write heap entry) next :=
      fun next member => ready_preserved head (ready next (by simp [member]))
    simpa only [List.length_cons, List.map_cons, List.cons_append, after, List.foldl_cons,
      Nat.add_comm entries.length 1, run_add, run_one env heap entry _ head, Option.bind_some] using
      ih (write heap entry) tail

theorem frame (heap : Heap) (entries : List Entry) (query : Address)
    (outside : ∀ entry ∈ entries, query ≠ entry.address) : after heap entries query = heap query := by
  induction entries generalizing heap with
  | nil => rfl
  | cons entry entries ih =>
    exact (ih (write heap entry) (fun next member => outside next (by simp [member]))).trans
      (write_frame heap entry query (outside entry (by simp)))

def Stored (heap : Heap) (entry : Entry) : Prop :=
  heap entry.address = some ⟨entry.type, true, some entry.value⟩

/-- Compatible aliases request the same final typed value. Conflicting
aliases still have an execution theorem, but not simultaneous output values. -/
def Compatible (entries : List Entry) : Prop :=
  ∀ a ∈ entries, ∀ b ∈ entries, a.address = b.address → a.type = b.type ∧ a.value = b.value

theorem write_preserves_stored (stored : Stored heap previous)
    (compatible : previous.address = entry.address → previous.type = entry.type ∧ previous.value = entry.value) :
    Stored (write heap entry) previous := by
  by_cases same : previous.address = entry.address
  · obtain ⟨types, values⟩ := compatible same
    simp [Stored, write, same, types, values]
  · exact (write_frame heap entry previous.address same).trans stored

theorem after_preserves_stored (stored : Stored heap previous)
    (aliases : ∀ entry ∈ entries, previous.address = entry.address →
      previous.type = entry.type ∧ previous.value = entry.value) :
    Stored (after heap entries) previous := by
  induction entries generalizing heap with
  | nil => exact stored
  | cons entry entries ih =>
    exact ih (write_preserves_stored stored (aliases entry (by simp)))
      (fun next member => aliases next (by simp [member]))

theorem outputs_stored (compatible : Compatible entries) :
    ∀ entry ∈ entries, Stored (after heap entries) entry := by
  induction entries generalizing heap with
  | nil => simp
  | cons entry entries ih =>
    intro selected member
    rcases List.mem_cons.mp member with same | member
    · subst selected
      apply after_preserves_stored (heap := write heap entry)
        (show Stored (write heap entry) entry by simp [Stored, write])
      intro next member same
      exact compatible entry (by simp) next (by simp [member]) same
    · exact ih (heap := write heap entry)
        (fun a ha b hb same => compatible a (by simp [ha]) b (by simp [hb]) same) selected member

end Rumoca.COutputAssignments
