import RumocaFMI3.CInterface
import RumocaFMI3.TimeProofs
import RumocaCore.FMI3.History

/-! The generated history blocks execute as the reference clock updates.
These contracts use typed, writable instance fields and arbitrary surrounding
memory. Public lifecycle/error bodies and adapter text binding remain separate. -/
namespace Rumoca.FMI3.HistoryProofs
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses
open CTree CMemory CBody
open Binary64 (toBits)

def cell (v : Binary64.Value) : Cell := ⟨.float64, true, some (.finite v)⟩
def write (heap : Heap) (p : Address) (name : String) (v : Binary64.Value) : Heap :=
  replace heap (p.member name) (cell v)

structure Stored (heap : Heap) (p : Address) (c : Time.Clock) : Prop where
  time : heap (p.member "time") = some (cell c.time)
  minimum : heap (p.member "timeMin") = some (cell c.minimum)
  eventTime : heap (p.member "eventTime") = some (cell c.eventTime)
  lastCompleted : heap (p.member "lastCompleted") = some (cell c.lastCompleted)

omit static in
theorem write_time (h : Stored heap p c) (v : Binary64.Value) :
    Stored (write heap p "time" v) p { c with time := v } := by
  rcases h with ⟨ht, hm, he, hl⟩
  constructor <;> simp_all [write, replace]

omit static in
theorem write_minimum (h : Stored heap p c) (v : Binary64.Value) :
    Stored (write heap p "timeMin" v) p { c with minimum := v } := by
  rcases h with ⟨ht, hm, he, hl⟩
  constructor <;> simp_all [write, replace]

omit static in
theorem write_event (h : Stored heap p c) (v : Binary64.Value) :
    Stored (write heap p "eventTime" v) p { c with eventTime := v } := by
  rcases h with ⟨ht, hm, he, hl⟩
  constructor <;> simp_all [write, replace]

omit static in
theorem write_completed (h : Stored heap p c) (v : Binary64.Value) :
    Stored (write heap p "lastCompleted" v) p { c with lastCompleted := v } := by
  rcases h with ⟨ht, hm, he, hl⟩
  constructor <;> simp_all [write, replace]

omit static in
theorem load_cell (hc : heap p = some (cell v)) : load heap p = some (.finite v) := by
  simp [load, hc, cell, convert, Value.finite]

theorem eval_field (env : Locals) (heap : Heap) (p : Address) (name : String)
    (hm : resolve env "m" = some (.pointer (some p))) :
    eval env heap (Runtime.field name) = load heap (p.member name) := by
  simp [Runtime.field, Runtime.v, CBody.eval, CBody.evalWith, CDeclaredMembers.memberValue, CDeclaredMembers.arrayAt, CDeclaredMembers.fieldAt, hm, Value.address]

theorem put_run (env : Locals) (heap : Heap) (p : Address) (name : String)
    (expr : Expr) (value old : Binary64.Value) (rest : List Stmt)
    (hm : resolve env "m" = some (.pointer (some p)))
    (hv : eval env heap expr = some (.finite value))
    (hc : heap (p.member name) = some (cell old)) :
    run 1 (.running (Runtime.put name expr :: rest) env heap) =
      some (.running rest env (write heap p name value)) := by
  have hs := store_float64 heap (p.member name) (some (.finite old)) (toBits value).val hc
  simp [run, CBody.next, CBody.nextWith, CBody.legacyExpressions, Runtime.put, Runtime.field, Runtime.v, CBody.lvalue, CBody.lvalueWith, CBody.eval, CBody.evalWith, hm, hv,
    Value.address, Value.finite, hs, write, cell]

def raiseHeap (heap : Heap) (p : Address) (name : String) (old value : Binary64.Value) : Heap :=
  if Binary64.units old < Binary64.units value then write heap p name value else heap

theorem raise_run (env : Locals) (heap : Heap) (p : Address) (name : String)
    (expr : Expr) (value old : Binary64.Value) (rest : List Stmt)
    (hm : resolve env "m" = some (.pointer (some p)))
    (hv : eval env heap expr = some (.finite value))
    (hc : heap (p.member name) = some (cell old)) :
    run (if Binary64.units old < Binary64.units value then 2 else 1)
      (.running (Runtime.raiseField name expr :: rest) env heap) =
      some (.running rest env (raiseHeap heap p name old value)) := by
  have hl := (eval_field env heap p name hm).trans (load_cell hc)
  have ht : Rumoca.Float64.test .lt (toBits old).val (toBits value).val = true ↔
      Binary64.units old < Binary64.units value := by
    rw [Rumoca.Float64.test_finite]
    exact Rumoca.Float64.value_lt_iff old value
  by_cases h : Binary64.units old < Binary64.units value
  · have hb := ht.mpr h
    have hp := put_run env heap p name expr value old rest hm hv hc
    simp only [h, ↓reduceIte, raiseHeap]
    change (do run 1 (← next (.running (Runtime.raiseField name expr :: rest) env heap))) = _
    simpa [Runtime.raiseField, Runtime.branch, Runtime.lt, next, nextWith, legacyExpressions,
      eval, evalWith, hl, hv,
      Value.finite, comparison, floatComparison, hb, boolean, Value.truth] using hp
  · have hb : Rumoca.Float64.test .lt (toBits old).val (toBits value).val = false :=
      Bool.eq_false_iff.mpr (fun hh => h (ht.mp hh))
    simp [run, CBody.next, CBody.nextWith, CBody.legacyExpressions, Runtime.raiseField, Runtime.branch, Runtime.lt, CBody.eval, CBody.evalWith, hl, hv,
      Value.finite, comparison, floatComparison, hb, boolean, Value.truth, h, raiseHeap]

omit static in
theorem raise_minimum (h : Stored heap p c) (v : Binary64.Value) :
    Stored (raiseHeap heap p "timeMin" c.minimum v) p
      { c with minimum := Time.maximum c.minimum v } := by
  unfold raiseHeap Time.maximum
  split
  · exact write_minimum h v
  · exact h

def initialHeap (heap : Heap) (p : Address) (start : Binary64.Value) : Heap :=
  write (write (write (write heap p "time" start) p "timeMin" start)
    p "eventTime" start) p "lastCompleted" start

def eventHeap (heap : Heap) (p : Address) (c : Time.Clock) : Heap :=
  raiseHeap (write heap p "eventTime" c.time) p "timeMin" c.minimum c.time

def completedHeap (heap : Heap) (p : Address) (c : Time.Clock) : Heap :=
  write (raiseHeap (write heap p "timeMin" c.eventTime) p "timeMin" c.eventTime c.lastCompleted)
    p "lastCompleted" c.time

omit static in
theorem initial_stored (h : Stored heap p c) (start : Binary64.Value) :
    Stored (initialHeap heap p start) p (Time.Clock.initial start) :=
  write_completed (write_event (write_minimum (write_time h start) start) start) start

omit static in
theorem event_stored (h : Stored heap p c) :
    Stored (eventHeap heap p c) p c.event := raise_minimum (write_event h c.time) c.time

omit static in
theorem completed_stored (h : Stored heap p c) :
    Stored (completedHeap heap p c) p c.completed :=
  write_completed (raise_minimum (write_minimum h c.eventTime) c.lastCompleted) c.time

theorem initial_reaches (env : Locals) (heap : Heap) (p : Address) (c : Time.Clock)
    (start : Binary64.Value) (rest : List Stmt) (h : Stored heap p c)
    (hm : resolve env "m" = some (.pointer (some p)))
    (hs : resolve env "startTime" = some (.finite start)) :
    Transition.Reaches machine.step (.running (Runtime.initialTime ++ rest) env heap)
      (.running rest env (initialHeap heap p start)) := by
  have ht := write_time h start
  have hn := write_minimum ht start
  have he := write_event hn start
  apply (run_reaches (put_run env heap p "time" (Runtime.v "startTime") start c.time _ hm hs h.time)).trans
  apply (run_reaches (put_run env _ p "timeMin" (Runtime.v "startTime") start c.minimum _ hm hs ht.minimum)).trans
  apply (run_reaches (put_run env _ p "eventTime" (Runtime.v "startTime") start c.eventTime _ hm hs hn.eventTime)).trans
  exact run_reaches (put_run env _ p "lastCompleted" (Runtime.v "startTime") start c.lastCompleted rest hm hs he.lastCompleted)

theorem event_reaches (env : Locals) (heap : Heap) (p : Address) (c : Time.Clock)
    (rest : List Stmt) (h : Stored heap p c)
    (hm : resolve env "m" = some (.pointer (some p))) :
    Transition.Reaches machine.step (.running (Runtime.eventTime ++ rest) env heap)
      (.running rest env (eventHeap heap p c)) := by
  have hv := (eval_field env heap p "time" hm).trans (load_cell h.time)
  have he := write_event h c.time
  apply (run_reaches (put_run env heap p "eventTime" _ c.time c.eventTime _ hm hv h.eventTime)).trans
  exact run_reaches (raise_run env _ p "timeMin" _ c.time c.minimum rest hm
    ((eval_field env _ p "time" hm).trans (load_cell he.time)) he.minimum)

theorem completed_reaches (env : Locals) (heap : Heap) (p : Address) (c : Time.Clock)
    (rest : List Stmt) (h : Stored heap p c)
    (hm : resolve env "m" = some (.pointer (some p))) :
    Transition.Reaches machine.step (.running (Runtime.completedTime ++ rest) env heap)
      (.running rest env (completedHeap heap p c)) := by
  have hv := (eval_field env heap p "eventTime" hm).trans (load_cell h.eventTime)
  have hn := write_minimum h c.eventTime
  have hr := raise_minimum hn c.lastCompleted
  apply (run_reaches (put_run env heap p "timeMin" _ c.eventTime c.minimum _ hm hv h.minimum)).trans
  apply (run_reaches (raise_run env _ p "timeMin" _ c.lastCompleted c.eventTime _ hm
    ((eval_field env _ p "lastCompleted" hm).trans (load_cell hn.lastCompleted)) hn.minimum)).trans
  exact run_reaches (put_run env _ p "lastCompleted" _ c.time c.lastCompleted rest hm
    ((eval_field env _ p "time" hm).trans (load_cell hr.time)) hr.lastCompleted)

theorem initial_correct (env : Locals) (heap : Heap) (p : Address) (c : Time.Clock)
    (start : Binary64.Value) (stop : Option Binary64.Value) (rest : List Stmt)
    (hc : Stored heap p c) (hm : resolve env "m" = some (.pointer (some p)))
    (hs : resolve env "startTime" = some (.finite start)) :
    Transition.Reaches machine.step (.running (Runtime.initialTime ++ rest) env heap)
      (.running rest env (initialHeap heap p start)) ∧
    Stored (initialHeap heap p start) p (Time.Clock.initial start) ∧
    Time.Represents (Time.History.initial start stop) (Time.Clock.initial start) :=
  ⟨initial_reaches env heap p c start rest hc hm hs,
   initial_stored hc start, Time.initial_represents start stop⟩

theorem event_correct (env : Locals) (heap : Heap) (p : Address) (c : Time.Clock)
    (h : Time.History) (rest : List Stmt) (hc : Stored heap p c)
    (hr : Time.Represents h c) (hm : resolve env "m" = some (.pointer (some p))) :
    Transition.Reaches machine.step (.running (Runtime.eventTime ++ rest) env heap)
      (.running rest env (eventHeap heap p c)) ∧
    Stored (eventHeap heap p c) p c.event ∧ Time.Represents h.event c.event :=
  ⟨event_reaches env heap p c rest hc hm, event_stored hc, Time.event_represents hr⟩

theorem completed_correct (env : Locals) (heap : Heap) (p : Address) (c : Time.Clock)
    (h : Time.History) (rest : List Stmt) (hc : Stored heap p c)
    (hr : Time.Represents h c) (hm : resolve env "m" = some (.pointer (some p))) :
    Transition.Reaches machine.step (.running (Runtime.completedTime ++ rest) env heap)
      (.running rest env (completedHeap heap p c)) ∧
    Stored (completedHeap heap p c) p c.completed ∧ Time.Represents h.completed c.completed :=
  ⟨completed_reaches env heap p c rest hc hm, completed_stored hc, Time.completed_represents hr⟩

omit static in
theorem write_frame (heap : Heap) (p q : Address) (name : String) (v : Binary64.Value)
    (hn : q ≠ p.member name) : write heap p name v q = heap q := replace_other _ _ _ _ hn

omit static in
theorem raise_frame (heap : Heap) (p q : Address) (name : String) (a b : Binary64.Value)
    (hn : q ≠ p.member name) : raiseHeap heap p name a b q = heap q := by
  unfold raiseHeap
  split
  · exact write_frame heap p q name b hn
  · rfl

omit static in
theorem initial_frame (heap : Heap) (p q : Address) (start : Binary64.Value)
    (ht : q ≠ p.member "time") (hm : q ≠ p.member "timeMin")
    (he : q ≠ p.member "eventTime") (hl : q ≠ p.member "lastCompleted") :
    initialHeap heap p start q = heap q := by
  simp only [initialHeap, write_frame _ _ _ _ _ hl, write_frame _ _ _ _ _ he,
    write_frame _ _ _ _ _ hm, write_frame _ _ _ _ _ ht]

omit static in
theorem event_frame (heap : Heap) (p q : Address) (c : Time.Clock)
    (he : q ≠ p.member "eventTime") (hm : q ≠ p.member "timeMin") :
    eventHeap heap p c q = heap q := by
  simp only [eventHeap, raise_frame _ _ _ _ _ _ hm, write_frame _ _ _ _ _ he]

omit static in
theorem completed_frame (heap : Heap) (p q : Address) (c : Time.Clock)
    (hl : q ≠ p.member "lastCompleted") (hm : q ≠ p.member "timeMin") :
    completedHeap heap p c q = heap q := by
  simp only [completedHeap, write_frame _ _ _ _ _ hl, raise_frame _ _ _ _ _ _ hm,
    write_frame _ _ _ _ _ hm]

/-- The cache invariant established by the generated blocks discharges the
history premise of the existing generated SetTime guard theorem. Optional
stop storage is separate experiment state and remains explicit. -/
theorem stored_guard_reference (heap : Heap) (p : Address) (c : Time.Clock)
    (h : Time.History) (time : Binary64.Value) (hc : Stored heap p c)
    (hr : Time.Represents h c)
    (hd : load heap (p.member "stopDefined") = some (boolean h.window.stopTime.isSome))
    (hs : ∀ bound, h.window.stopTime = some bound →
      load heap (p.member "stop") = some (.finite bound)) :
    eval (TimeProofs.locals p (toBits time).val) heap Runtime.invalidTime =
      some (boolean false) ↔ h.window.Admissible time :=
  TimeProofs.guard_reference heap p h.window c.minimum time hr.minimum
    (load_cell hc.minimum) hd hs

end Rumoca.FMI3.HistoryProofs
