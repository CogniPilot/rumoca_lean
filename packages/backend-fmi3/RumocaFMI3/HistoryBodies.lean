import RumocaFMI3.CInterface
import RumocaFMI3.HistoryProofs
import RumocaFMI3.LifecycleGuard

/-! Successful public ME event-entry and completed-step bodies. Execution
includes the instance/lifecycle guards, caller outputs, history updates and
mode/return writes. Invalid-call logging and the native ABI remain separate. -/
namespace Rumoca.FMI3.HistoryBodies
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses
open CTree CMemory CBody

def parameters (p : Address) : Locals := fun name =>
  if name = "instance" then some (.pointer (some p)) else none

def completedParameters (p event terminate : Address) (noSetState : Bool) : Locals := fun name =>
  if name = "instance" then some (.pointer (some p))
  else if name = "enterEventMode" then some (.pointer (some event))
  else if name = "terminateSimulation" then some (.pointer (some terminate))
  else if name = "noSetFMUStatePriorToCurrentPoint" then some (boolean noSetState)
  else none

def locals (env : Locals) (p : Address) : Locals :=
  CBody.bind env "m" (.pointer (some p))

theorem continuous_prefix (env : Locals) (heap : Heap) (p : Address)
    (cmd : Command) (rest : List Stmt)
    (hc : cmd = .enterEvent ∨ cmd = .completedStep)
    (hp : env "instance" = some (.pointer (some p))) (hn : env "m" = none)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer 3)) :
    run 3 (.running (Runtime.require cmd ++ rest) env heap) =
      some (.running rest (locals env p) heap) := by
  have ha : Reference.Allowed cmd .me .continuous := by
    rcases hc with rfl | rfl <;> simp [Reference.Allowed]
  exact LifecycleGuard.accept env heap p cmd .me .continuous rest hp hn hk hm ha

theorem return_ok (env : Locals) (heap : Heap)
    (ho : resolve env "fmi3OK" = some (.integer 0)) :
    run 1 (.running [Runtime.ok] env heap) = some (.returned ⟨.integer 0, heap⟩) := by
  simp [run, next, Runtime.ok, Runtime.ret, Runtime.v, eval, ho]

def eventHeap (heap : Heap) (p : Address) (c : Time.Clock) : Heap :=
  replace (HistoryProofs.eventHeap heap p c) (p.member "mode")
    ⟨.int32, true, some (.integer 2)⟩

omit static in
theorem event_frame (heap : Heap) (p q : Address) (c : Time.Clock)
    (he : q ≠ p.member "eventTime") (ht : q ≠ p.member "timeMin")
    (hm : q ≠ p.member "mode") : eventHeap heap p c q = heap q := by
  simp only [eventHeap, replace_other _ _ _ _ hm, HistoryProofs.event_frame _ _ _ _ he ht]

omit static in
theorem event_stored (hs : HistoryProofs.Stored heap p c) :
    HistoryProofs.Stored (eventHeap heap p c) p c.event := by
  rcases HistoryProofs.event_stored hs with ⟨ht, hn, he, hl⟩
  constructor <;> simp_all [eventHeap, replace]

set_option maxRecDepth 10000 in
theorem event_reaches (m : Solve.FMI3Model source) (sig : Signature)
    (hsig : sig.name = "fmi3EnterEventMode") (heap : Heap) (p : Address) (c : Time.Clock)
    (hc : HistoryProofs.Stored heap p c)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer 3)⟩) :
    Transition.Reaches machine.step (.running (Runtime.body m sig) (parameters p) heap)
      (.returned ⟨.integer 0, eventHeap heap p c⟩) := by
  have hmode : load heap (p.member "mode") = some (.integer 3) := by simp [load, hm, convert]
  have hp := continuous_prefix (parameters p) heap p .enterEvent
    (Runtime.eventTime ++ [Runtime.setMode .event, Runtime.ok]) (Or.inl rfl)
    (by simp [parameters]) (by simp [parameters]) hk hmode
  have hb := HistoryProofs.event_reaches (locals (parameters p) p) heap p c
    [Runtime.setMode .event, Runtime.ok] hc (by simp [locals, CBody.bind, resolve])
  have hframe : HistoryProofs.eventHeap heap p c (p.member "mode") =
      some ⟨.int32, true, some (.integer 3)⟩ := by
    rw [HistoryProofs.event_frame heap p (p.member "mode") c (by simp) (by simp), hm]
  have ht : run 2 (.running [Runtime.setMode .event, Runtime.ok]
      (locals (parameters p) p) (HistoryProofs.eventHeap heap p c)) =
      some (.returned ⟨.integer 0, eventHeap heap p c⟩) := by
    simp [Runtime.setMode, Runtime.put, Runtime.mode, Mode.code, Runtime.field,
      Runtime.v, Runtime.n, Runtime.ok, Runtime.ret, run, next, eval, lvalue,
      locals, parameters, CBody.bind, resolve, constants, Value.address,
      store, hframe, convert, eventHeap]
  have hbody : Runtime.body m sig = Runtime.require .enterEvent ++
      (Runtime.eventTime ++ [Runtime.setMode .event, Runtime.ok]) := by
    simp [Runtime.body, hsig, List.append_assoc]
  rw [hbody]
  exact (run_reaches hp).trans (hb.trans (run_reaches ht))

/-- Writable Boolean outputs may be uninitialized and may alias one another. -/
def BoolWritable (heap : Heap) (p : Address) : Prop :=
  ∃ old, heap p = some ⟨.boolean, true, old⟩

def zero (heap : Heap) (p : Address) : Heap :=
  replace heap p ⟨.boolean, true, some (.integer 0)⟩

omit static in
theorem zero_store (h : BoolWritable heap p) :
    store heap p (.integer 0) = some (zero heap p) := by
  obtain ⟨old, h⟩ := h
  simp [store, h, convert, Value.truth, zero]

omit static in
theorem zero_writable (h : BoolWritable heap q) (p : Address) :
    BoolWritable (zero heap p) q := by
  by_cases he : q = p
  · subst q; exact ⟨some (.integer 0), by simp [zero]⟩
  · obtain ⟨old, h⟩ := h
    exact ⟨old, by rw [zero, replace_other _ _ _ _ he, h]⟩

omit static in
theorem zero_frame (heap : Heap) (p q : Address) (hn : q ≠ p) :
    zero heap p q = heap q := replace_other _ _ _ _ hn

omit static in
theorem field_ne_output (p out : Address) (name : String) (hn : out.block ≠ p.block) :
    p.member name ≠ out := by
  intro h
  exact hn (congrArg Address.block h).symm

omit static in
theorem zero_stored (h : HistoryProofs.Stored heap p c) (out : Address)
    (hn : out.block ≠ p.block) : HistoryProofs.Stored (zero heap out) p c := by
  rcases h with ⟨ht, hm, he, hl⟩
  constructor <;>
    simp_all only [zero_frame _ _ _ (field_ne_output _ _ _ hn)]

def outputsHeap (heap : Heap) (event terminate : Address) : Heap := zero (zero heap event) terminate

set_option maxRecDepth 10000 in
theorem outputs_run (heap : Heap) (p event terminate : Address) (flag : Bool) (rest : List Stmt)
    (he : BoolWritable heap event) (ht : BoolWritable heap terminate) :
    run 3 (.running ([Runtime.pointerCheck ["enterEventMode", "terminateSimulation"],
        Runtime.out "enterEventMode" (Runtime.n 0), Runtime.out "terminateSimulation" (Runtime.n 0)] ++ rest)
      (locals (completedParameters p event terminate flag) p) heap) =
      some (.running rest (locals (completedParameters p event terminate flag) p)
        (outputsHeap heap event terminate)) := by
  have heStore := zero_store he
  have htStore := zero_store (zero_writable ht event)
  simp [run, next, Runtime.pointerCheck, Runtime.reject, Runtime.any, Runtime.branch,
    Runtime.out, Runtime.v, Runtime.n, Runtime.negate, Runtime.either, eval, lvalue,
    locals, completedParameters, CBody.bind, resolve, constants, Value.address,
    Value.truth, boolean, heStore, htStore, outputsHeap]

def completedHeap (heap : Heap) (p event terminate : Address) (c : Time.Clock) : Heap :=
  HistoryProofs.completedHeap (outputsHeap heap event terminate) p c

omit static in
theorem outputs_stored (hc : HistoryProofs.Stored heap p c) (event terminate : Address)
    (he : event.block ≠ p.block) (ht : terminate.block ≠ p.block) :
    HistoryProofs.Stored (outputsHeap heap event terminate) p c :=
  zero_stored (zero_stored hc event he) terminate ht

omit static in
theorem completed_stored (hc : HistoryProofs.Stored heap p c) (event terminate : Address)
    (he : event.block ≠ p.block) (ht : terminate.block ≠ p.block) :
    HistoryProofs.Stored (completedHeap heap p event terminate c) p c.completed :=
  HistoryProofs.completed_stored (outputs_stored hc event terminate he ht)

omit static in
theorem completed_frame (heap : Heap) (p event terminate q : Address) (c : Time.Clock)
    (hl : q ≠ p.member "lastCompleted") (hm : q ≠ p.member "timeMin")
    (he : q ≠ event) (ht : q ≠ terminate) :
    completedHeap heap p event terminate c q = heap q := by
  simp only [completedHeap, HistoryProofs.completed_frame _ _ _ _ hl hm,
    outputsHeap, zero_frame _ _ _ ht, zero_frame _ _ _ he]

set_option maxRecDepth 10000 in
theorem completed_reaches (m : Solve.FMI3Model source) (sig : Signature)
    (hsig : sig.name = "fmi3CompletedIntegratorStep") (heap : Heap) (p event terminate : Address)
    (flag : Bool) (c : Time.Clock) (hc : HistoryProofs.Stored heap p c)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer 3))
    (he : BoolWritable heap event) (ht : BoolWritable heap terminate)
    (hne : event.block ≠ p.block) (hnt : terminate.block ≠ p.block) :
    Transition.Reaches machine.step
      (.running (Runtime.body m sig) (completedParameters p event terminate flag) heap)
      (.returned ⟨.integer 0, completedHeap heap p event terminate c⟩) := by
  let env := completedParameters p event terminate flag
  let rest := [Runtime.pointerCheck ["enterEventMode", "terminateSimulation"],
    Runtime.out "enterEventMode" (Runtime.n 0), Runtime.out "terminateSimulation" (Runtime.n 0)] ++
    Runtime.completedTime ++ [Runtime.ok]
  have hp := continuous_prefix env heap p .completedStep rest (Or.inr rfl)
    (by simp [env, completedParameters]) (by simp [env, completedParameters]) hk hm
  have ho := outputs_run heap p event terminate flag (Runtime.completedTime ++ [Runtime.ok]) he ht
  have hb := HistoryProofs.completed_reaches (locals env p) (outputsHeap heap event terminate) p c
    [Runtime.ok] (outputs_stored hc event terminate hne hnt)
    (by simp [locals, CBody.bind, resolve])
  have hr := return_ok (locals env p) (completedHeap heap p event terminate c)
    (by simp [locals, env, completedParameters, CBody.bind, resolve, constants])
  have hbody : Runtime.body m sig = Runtime.require .completedStep ++ rest := by
    simp [Runtime.body, hsig, rest, List.append_assoc]
  rw [hbody]
  exact (run_reaches hp).trans ((run_reaches ho).trans (hb.trans (run_reaches hr)))

omit static in
theorem event_mode (heap : Heap) (p : Address) (c : Time.Clock) :
    load (eventHeap heap p c) (p.member "mode") =
      some (.integer (nextMode .enterEvent .me .continuous).code) := by
  change load (eventHeap heap p c) (p.member "mode") = some (.integer 2)
  simp [eventHeap, load, convert]

omit static in
theorem completed_mode (heap : Heap) (p event terminate : Address) (c : Time.Clock)
    (hm : load heap (p.member "mode") = some (.integer 3))
    (he : event.block ≠ p.block) (ht : terminate.block ≠ p.block) :
    load (completedHeap heap p event terminate c) (p.member "mode") =
      some (.integer (nextMode .completedStep .me .continuous).code) := by
  have hf := completed_frame heap p event terminate (p.member "mode") c
    (by simp) (by simp) (field_ne_output p event "mode" he) (field_ne_output p terminate "mode" ht)
  simpa only [load, hf] using hm

omit static in
theorem completed_outputs (heap : Heap) (p event terminate : Address) (c : Time.Clock)
    (he : event.block ≠ p.block) (ht : terminate.block ≠ p.block) :
    load (completedHeap heap p event terminate c) event = some (boolean false) ∧
    load (completedHeap heap p event terminate c) terminate = some (boolean false) := by
  have hef := HistoryProofs.completed_frame (outputsHeap heap event terminate) p event c
    (Ne.symm (field_ne_output p event "lastCompleted" he))
    (Ne.symm (field_ne_output p event "timeMin" he))
  have htf := HistoryProofs.completed_frame (outputsHeap heap event terminate) p terminate c
    (Ne.symm (field_ne_output p terminate "lastCompleted" ht))
    (Ne.symm (field_ne_output p terminate "timeMin" ht))
  simp only [completedHeap, load, hef, htf]
  simp [outputsHeap, zero, replace, convert, Value.truth, boolean]

omit static in
theorem state_ne_field (p : Address) (name : String) : StateProofs.stateAddress p ≠ p.member name := by
  intro h
  have hl := congrArg (fun q : Address => q.members.length) h
  simp [StateProofs.stateAddress, Address.member] at hl

omit static in
theorem event_model (h : StateProofs.Represents heap p state) (c : Time.Clock) :
    StateProofs.Represents (eventHeap heap p c) p state := by
  have hf := event_frame heap p (StateProofs.stateAddress p) c
    (state_ne_field p "eventTime") (state_ne_field p "timeMin") (state_ne_field p "mode")
  simpa only [StateProofs.Represents, load, hf] using h

omit static in
theorem completed_model (h : StateProofs.Represents heap p state) (c : Time.Clock)
    (event terminate : Address) (he : event.block ≠ p.block) (ht : terminate.block ≠ p.block) :
    StateProofs.Represents (completedHeap heap p event terminate c) p state := by
  have hn (out : Address) (hne : out.block ≠ p.block) : StateProofs.stateAddress p ≠ out := by
    intro h
    apply hne
    simpa [StateProofs.stateAddress, Address.member] using (congrArg Address.block h).symm
  have hf := completed_frame heap p event terminate (StateProofs.stateAddress p) c
    (state_ne_field p "lastCompleted") (state_ne_field p "timeMin") (hn event he) (hn terminate ht)
  simpa only [StateProofs.Represents, load, hf] using h

noncomputable section
theorem event_behaviors (m : Solve.FMI3Model source) (sig : Signature)
    (hsig : sig.name = "fmi3EnterEventMode") (heap : Heap) (p : Address) (c : Time.Clock)
    (hc : HistoryProofs.Stored heap p c)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer 3)⟩) (b) :
    (CCalls.machine (CallProofs.linked m)).Behaves
      (.body (.running (Runtime.body m sig) (parameters p) heap) "fmi3Status" .done) b ↔
      b = .terminates ⟨.integer 0, eventHeap heap p c⟩ :=
  CCalls.body_behaviors_of_reaches _ (event_reaches m sig hsig heap p c hc hk hm)
    (by simp [CCalls.returnCast, CBody.cast, convert]) b

theorem completed_behaviors (m : Solve.FMI3Model source) (sig : Signature)
    (hsig : sig.name = "fmi3CompletedIntegratorStep") (heap : Heap) (p event terminate : Address)
    (flag : Bool) (c : Time.Clock) (hc : HistoryProofs.Stored heap p c)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer 3))
    (he : BoolWritable heap event) (ht : BoolWritable heap terminate)
    (hne : event.block ≠ p.block) (hnt : terminate.block ≠ p.block) (b) :
    (CCalls.machine (CallProofs.linked m)).Behaves
      (.body (.running (Runtime.body m sig) (completedParameters p event terminate flag) heap)
        "fmi3Status" .done) b ↔
      b = .terminates ⟨.integer 0, completedHeap heap p event terminate c⟩ :=
  CCalls.body_behaviors_of_reaches _
    (completed_reaches m sig hsig heap p event terminate flag c hc hk hm he ht hne hnt)
    (by simp [CCalls.returnCast, CBody.cast, convert]) b

/-- Composes the full emitted event-entry body with independent reference
history, reference lifecycle mode and the shared Solve/ME model state. -/
theorem event_correct (m : Solve.FMI3Model source) (sig : Signature)
    (hsig : sig.name = "fmi3EnterEventMode") (heap : Heap) (p : Address)
    (c : Time.Clock) (h : Time.History) (state : ModelExchange.State)
    (hc : HistoryProofs.Stored heap p c) (hr : Time.Represents h c)
    (hx : StateProofs.Represents heap p state)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer 3)⟩) :
    (∀ b, (CCalls.machine (CallProofs.linked m)).Behaves
      (.body (.running (Runtime.body m sig) (parameters p) heap) "fmi3Status" .done) b ↔
      b = .terminates ⟨.integer 0, eventHeap heap p c⟩) ∧
    HistoryProofs.Stored (eventHeap heap p c) p c.event ∧ Time.Represents h.event c.event ∧
    StateProofs.Represents (eventHeap heap p c) p state ∧
    load (eventHeap heap p c) (p.member "mode") =
      some (.integer (nextMode .enterEvent .me .continuous).code) :=
  ⟨event_behaviors m sig hsig heap p c hc hk hm, event_stored hc,
    Time.event_represents hr, event_model hx c, event_mode heap p c⟩

/-- Composes the full emitted completion body with the positional history
update, unchanged shared model and lifecycle mode, and both false outputs. -/
theorem completed_correct (m : Solve.FMI3Model source) (sig : Signature)
    (hsig : sig.name = "fmi3CompletedIntegratorStep") (heap : Heap) (p event terminate : Address)
    (flag : Bool) (c : Time.Clock) (h : Time.History) (state : ModelExchange.State)
    (hc : HistoryProofs.Stored heap p c) (hr : Time.Represents h c)
    (hx : StateProofs.Represents heap p state)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer 3))
    (he : BoolWritable heap event) (ht : BoolWritable heap terminate)
    (hne : event.block ≠ p.block) (hnt : terminate.block ≠ p.block) :
    (∀ b, (CCalls.machine (CallProofs.linked m)).Behaves
      (.body (.running (Runtime.body m sig) (completedParameters p event terminate flag) heap)
        "fmi3Status" .done) b ↔
      b = .terminates ⟨.integer 0, completedHeap heap p event terminate c⟩) ∧
    HistoryProofs.Stored (completedHeap heap p event terminate c) p c.completed ∧
    Time.Represents h.completed c.completed ∧
    StateProofs.Represents (completedHeap heap p event terminate c) p state ∧
    load (completedHeap heap p event terminate c) (p.member "mode") =
      some (.integer (nextMode .completedStep .me .continuous).code) ∧
    load (completedHeap heap p event terminate c) event = some (boolean false) ∧
    load (completedHeap heap p event terminate c) terminate = some (boolean false) :=
  ⟨completed_behaviors m sig hsig heap p event terminate flag c hc hk hm he ht hne hnt,
    completed_stored hc event terminate hne hnt, Time.completed_represents hr,
    completed_model hx c event terminate hne hnt, completed_mode heap p event terminate c hm hne hnt,
    completed_outputs heap p event terminate c hne hnt⟩

end
end Rumoca.FMI3.HistoryBodies
