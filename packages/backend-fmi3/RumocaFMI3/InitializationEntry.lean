import RumocaCore.FMI3.Initialization
import RumocaFMI3.InitializationBodies

/-! The complete successful initialization-entry body for both ME and CS.
Validation refines the independent finite profile; generated clock, stop and
mode writes establish the reference history and the existing SetTime guard.
The initial model state and unrelated memory are preserved. Supplied parameter
bindings and typed writable storage are explicit premises. Rejected calls,
public ABI entry and actual printed-adapter binding remain open. -/
namespace Rumoca.FMI3.InitializationEntry
private local instance targetInterface : CInterface := cInterface
open CTree CMemory CBody Initialization
open Binary64 (toBits)

def parameters (p : Address) (args : Arguments) : Locals := fun name =>
  if name = "instance" then some (.pointer (some p))
  else if name = "startTime" then some (.finite args.start)
  else if name = "toleranceDefined" then some (boolean args.toleranceDefined)
  else if name = "tolerance" then some (.float64 args.tolerance)
  else if name = "stopTimeDefined" then some (boolean args.stopDefined)
  else if name = "stopTime" then some (.float64 args.stop)
  else none

def locals (p : Address) (args : Arguments) : Locals :=
  bind (parameters p args) "m" (.pointer (some p))

def guard : Expr := Runtime.any [Runtime.negate (Runtime.finite (Runtime.v "startTime")),
  Runtime.both (Runtime.v "toleranceDefined")
    (Runtime.either (Runtime.negate (Runtime.finite (Runtime.v "tolerance")))
      (Runtime.le (Runtime.v "tolerance") (Runtime.n 0))),
  Runtime.both (Runtime.v "stopTimeDefined")
    (Runtime.either (Runtime.negate (Runtime.finite (Runtime.v "stopTime")))
      (Runtime.le (Runtime.v "stopTime") (Runtime.v "startTime")))]

def rejects (args : Arguments) : Bool :=
  (args.toleranceDefined && !above args.tolerance Binary64.positiveZero) ||
  (args.stopDefined && !above args.stop args.start)

theorem rejects_iff (args : Arguments) : rejects args = false ↔ args.Admissible := by
  simp [rejects, Arguments.Admissible, ← above_iff, Bool.and_eq_false_imp]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem guard_eval (heap : Heap) (p : Address) (args : Arguments) :
    eval (locals p args) heap guard = some (boolean (rejects args)) := by
  have hf := Value.isFinite_finite args.start
  change Value.isFinite (.float64 (toBits args.start).val) = some true at hf
  have htol : Value.isFinite (.float64 args.tolerance) = some (finiteBits args.tolerance) := rfl
  have hstop : Value.isFinite (.float64 args.stop) = some (finiteBits args.stop) := rfl
  simp [guard, Runtime.any, Runtime.either, Runtime.both, Runtime.negate,
    Runtime.finite, Runtime.call, Runtime.le, Runtime.v, Runtime.n, eval,
    locals, parameters, CBody.bind, resolve, constants, comparison, floatComparison,
    convert, Value.finite, hf, htol, hstop, rejects, above]
  all_goals
    cases htd : args.toleranceDefined <;> cases hsd : args.stopDefined <;>
      cases htf : finiteBits args.tolerance <;> cases hsf : finiteBits args.stop <;>
      cases htc : Rumoca.Float64.test .le args.tolerance (toBits Binary64.positiveZero).val <;>
      cases hsc : Rumoca.Float64.test .le args.stop (toBits args.start).val <;>
      simp_all [boolean, Value.truth]

theorem guard_reference (heap : Heap) (p : Address) (args : Arguments) :
    eval (locals p args) heap guard = some (boolean false) ↔ args.Admissible := by
  rw [guard_eval]
  have hb : ∀ b, boolean b = boolean false ↔ b = false := by intro b; cases b <;> decide
  rw [Option.some.injEq, hb, rejects_iff]

def finalHeap (heap : Heap) (p : Address) (args : Arguments) : Heap :=
  replace (replace (replace (HistoryProofs.initialHeap heap p args.start)
    (p.member "stop") ⟨.float64, true, some (.float64 args.stop)⟩)
    (p.member "stopDefined") ⟨.boolean, true, some (boolean args.stopDefined)⟩)
    (p.member "mode") ⟨.int32, true, some (.integer 1)⟩

theorem prefix_run (heap : Heap) (p : Address) (args : Arguments) (kind : Kind)
    (rest : List Stmt) (ha : args.Admissible)
    (hk : load heap (p.member "kind") = some (.integer (InitializationBodies.kindCode kind)))
    (hm : load heap (p.member "mode") = some (.integer 0)) :
    run 4 (.running (Runtime.require .enterInitialization ++
      [Runtime.reject guard "Invalid initialization times or tolerance"] ++ rest)
      (parameters p args) heap) = some (.running rest (locals p args) heap) := by
  have hk' : load heap (p.member "kind") = some (.integer kind.code) := by
    cases kind <;> exact hk
  have hp := LifecycleGuard.accept (parameters p args) heap p .enterInitialization kind
    .instantiated (Runtime.reject guard "Invalid initialization times or tolerance" :: rest)
    (by simp [parameters]) (by simp [parameters]) hk' hm rfl
  have hg := (guard_reference heap p args).mpr ha
  rw [show 4 = 3 + 1 from rfl, run_add]
  simp only [List.append_assoc, List.singleton_append] at hp ⊢
  rw [hp]
  simpa only [locals] using
    (show run 1 (.running (Runtime.reject guard "Invalid initialization times or tolerance" :: rest)
        (locals p args) heap) = some (.running rest (locals p args) heap) by
      simp [Runtime.reject, Runtime.branch, run, next, hg, boolean, Value.truth])

set_option maxRecDepth 10000 in
theorem body_reaches (m : Solve.FMI3Model source) (sig : Signature)
    (hsig : sig.name = "fmi3EnterInitializationMode") (heap : Heap) (p : Address)
    (args : Arguments) (kind : Kind) (clock : Time.Clock)
    (stopOld flagOld : Option Value) (ha : args.Admissible)
    (hc : HistoryProofs.Stored heap p clock)
    (hk : load heap (p.member "kind") = some (.integer (InitializationBodies.kindCode kind)))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer 0)⟩)
    (hs : heap (p.member "stop") = some ⟨.float64, true, stopOld⟩)
    (hd : heap (p.member "stopDefined") = some ⟨.boolean, true, flagOld⟩) :
    Transition.Reaches machine.step
      (.running (Runtime.body m sig) (parameters p args) heap)
      (.returned ⟨.integer 0, finalHeap heap p args⟩) := by
  let tail := [Runtime.put "stop" (Runtime.v "stopTime"),
    Runtime.put "stopDefined" (Runtime.v "stopTimeDefined"),
    Runtime.setMode .initialization, Runtime.ok]
  have hmode : load heap (p.member "mode") = some (.integer 0) := by
    simp [load, hm, convert]
  have hp := prefix_run heap p args kind (Runtime.initialTime ++ tail) ha hk hmode
  have hh := HistoryProofs.initial_reaches (locals p args) heap p clock args.start tail hc
    (by simp [locals, CBody.bind, resolve])
    (by simp [locals, parameters, CBody.bind, resolve])
  have frame (name : String) (ht : name ≠ "time") (hn : name ≠ "timeMin")
      (he : name ≠ "eventTime") (hl : name ≠ "lastCompleted") :
      HistoryProofs.initialHeap heap p args.start (p.member name) = heap (p.member name) :=
    HistoryProofs.initial_frame _ _ _ _ (by simpa) (by simpa) (by simpa) (by simpa)
  have hs' := (frame "stop" (by decide) (by decide) (by decide) (by decide)).trans hs
  have hd' := (frame "stopDefined" (by decide) (by decide) (by decide) (by decide)).trans hd
  have hm' := (frame "mode" (by decide) (by decide) (by decide) (by decide)).trans hm
  have ht : run 4 (.running tail (locals p args) (HistoryProofs.initialHeap heap p args.start)) =
      some (.returned ⟨.integer 0, finalHeap heap p args⟩) := by
    cases hflag : args.stopDefined <;>
      simp [tail, Runtime.setMode, Runtime.put, Runtime.mode, Mode.code, Runtime.field,
        Runtime.v, Runtime.n, Runtime.ok, Runtime.ret, run, next, eval, lvalue,
        locals, parameters, CBody.bind, resolve, constants, Value.address, boolean, Value.truth,
        store, hs', hd', hm', convert, finalHeap, replace, hflag]
  have hb : Runtime.body m sig = Runtime.require .enterInitialization ++
      [Runtime.reject guard "Invalid initialization times or tolerance"] ++
        (Runtime.initialTime ++ tail) := by
    simp [Runtime.body, hsig, guard, tail, List.append_assoc]
  rw [hb]
  exact (run_reaches hp).trans (hh.trans (run_reaches ht))

theorem frame (heap : Heap) (p q : Address) (args : Arguments)
    (ht : q ≠ p.member "time") (hn : q ≠ p.member "timeMin")
    (he : q ≠ p.member "eventTime") (hl : q ≠ p.member "lastCompleted")
    (hs : q ≠ p.member "stop") (hd : q ≠ p.member "stopDefined")
    (hm : q ≠ p.member "mode") : finalHeap heap p args q = heap q := by
  simp only [finalHeap, replace_other _ _ _ _ hm, replace_other _ _ _ _ hd,
    replace_other _ _ _ _ hs, HistoryProofs.initial_frame _ _ _ _ ht hn he hl]

theorem stored (hc : HistoryProofs.Stored heap p clock) (args : Arguments) :
    HistoryProofs.Stored (finalHeap heap p args) p (Time.Clock.initial args.start) := by
  rcases HistoryProofs.initial_stored hc args.start with ⟨ht, hn, he, hl⟩
  constructor <;> simp_all [finalHeap, replace]

theorem model (hx : StateProofs.Represents heap p state) (args : Arguments) :
    StateProofs.Represents (finalHeap heap p args) p state := by
  have hf := frame heap p (StateProofs.stateAddress p) args
    (HistoryBodies.state_ne_field p "time") (HistoryBodies.state_ne_field p "timeMin")
    (HistoryBodies.state_ne_field p "eventTime") (HistoryBodies.state_ne_field p "lastCompleted")
    (HistoryBodies.state_ne_field p "stop") (HistoryBodies.state_ne_field p "stopDefined")
    (HistoryBodies.state_ne_field p "mode")
  simpa only [StateProofs.Represents, load, hf] using hx

theorem mode (heap : Heap) (p : Address) (args : Arguments) (kind : Kind) :
    load (finalHeap heap p args) (p.member "mode") =
      some (.integer (nextMode .enterInitialization kind .instantiated).code) := by
  have hr : nextMode .enterInitialization kind .instantiated = .initialization := by
    cases kind <;> rfl
  rw [hr]
  simp [finalHeap, load, replace, convert, Mode.code]

theorem stop (heap : Heap) (p : Address) (args : Arguments) :
    load (finalHeap heap p args) (p.member "stop") = some (.float64 args.stop) ∧
    load (finalHeap heap p args) (p.member "stopDefined") = some (boolean args.stopDefined) := by
  cases hd : args.stopDefined <;> simp [finalHeap, replace, load, convert, boolean, Value.truth, hd]

theorem time_guard (heap : Heap) (p : Address) (args : Arguments) (clock : Time.Clock)
    (ha : args.Admissible) (hc : HistoryProofs.Stored heap p clock) (time : Binary64.Value) :
    eval (TimeProofs.locals p (toBits time).val) (finalHeap heap p args) Runtime.invalidTime =
      some (boolean false) ↔ (Time.Window.initial args.start args.stopTime).Admissible time := by
  apply HistoryProofs.stored_guard_reference (finalHeap heap p args) p
    (Time.Clock.initial args.start) (Time.History.initial args.start args.stopTime) time
    (stored hc args) (Time.initial_represents args.start args.stopTime)
  · simpa only [Time.History.initial, Time.Window.initial, stopTime_defined args ha]
      using (stop heap p args).2
  · intro bound hb
    have hbits := stopTime_bits args ha bound hb
    simpa only [Value.finite, hbits] using (stop heap p args).1

noncomputable section
theorem behaviors (m : Solve.FMI3Model source) (sig : Signature)
    (hsig : sig.name = "fmi3EnterInitializationMode") (heap : Heap) (p : Address)
    (args : Arguments) (kind : Kind) (clock : Time.Clock)
    (stopOld flagOld : Option Value) (ha : args.Admissible)
    (hc : HistoryProofs.Stored heap p clock)
    (hk : load heap (p.member "kind") = some (.integer (InitializationBodies.kindCode kind)))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer 0)⟩)
    (hs : heap (p.member "stop") = some ⟨.float64, true, stopOld⟩)
    (hd : heap (p.member "stopDefined") = some ⟨.boolean, true, flagOld⟩) (b) :
    (CCalls.machine (CallProofs.linked m)).Behaves
      (.body (.running (Runtime.body m sig) (parameters p args) heap) "fmi3Status" .done) b ↔
      b = .terminates ⟨.integer 0, finalHeap heap p args⟩ :=
  CCalls.body_behaviors_of_reaches _
    (body_reaches m sig hsig heap p args kind clock stopOld flagOld ha hc hk hm hs hd)
    (by simp [CCalls.returnCast, CBody.cast, convert]) b

theorem correct (m : Solve.FMI3Model source) (sig : Signature)
    (hsig : sig.name = "fmi3EnterInitializationMode") (heap : Heap) (p : Address)
    (args : Arguments) (kind : Kind) (clock : Time.Clock) (state : ModelExchange.State)
    (stopOld flagOld : Option Value) (ha : args.Admissible)
    (hc : HistoryProofs.Stored heap p clock) (hx : StateProofs.Represents heap p state)
    (hk : load heap (p.member "kind") = some (.integer (InitializationBodies.kindCode kind)))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer 0)⟩)
    (hs : heap (p.member "stop") = some ⟨.float64, true, stopOld⟩)
    (hd : heap (p.member "stopDefined") = some ⟨.boolean, true, flagOld⟩) :
    (∀ b, (CCalls.machine (CallProofs.linked m)).Behaves
      (.body (.running (Runtime.body m sig) (parameters p args) heap) "fmi3Status" .done) b ↔
      b = .terminates ⟨.integer 0, finalHeap heap p args⟩) ∧
    StateProofs.Represents (finalHeap heap p args) p state ∧
    HistoryProofs.Stored (finalHeap heap p args) p (Time.Clock.initial args.start) ∧
    Time.Represents (Time.History.initial args.start args.stopTime) (Time.Clock.initial args.start) ∧
    load (finalHeap heap p args) (p.member "mode") =
      some (.integer (nextMode .enterInitialization kind .instantiated).code) ∧
    (∀ time, eval (TimeProofs.locals p (toBits time).val) (finalHeap heap p args) Runtime.invalidTime =
      some (boolean false) ↔ (Time.Window.initial args.start args.stopTime).Admissible time) :=
  ⟨behaviors m sig hsig heap p args kind clock stopOld flagOld ha hc hk hm hs hd,
   model hx args, stored hc args, Time.initial_represents args.start args.stopTime,
   mode heap p args kind, time_guard heap p args clock ha hc⟩

/-- Sequential entry and exit use the same intermediate heap. This composes
the two complete successful bodies; arbitrary lifecycle traces remain separate. -/
theorem then_exit (m : Solve.FMI3Model source) (enterSig exitSig : Signature)
    (henter : enterSig.name = "fmi3EnterInitializationMode")
    (hexit : exitSig.name = "fmi3ExitInitializationMode") (heap : Heap) (p : Address)
    (args : Arguments) (kind : Kind) (clock : Time.Clock) (state : ModelExchange.State)
    (stopOld flagOld : Option Value) (ha : args.Admissible)
    (hc : HistoryProofs.Stored heap p clock) (hx : StateProofs.Represents heap p state)
    (hk : load heap (p.member "kind") = some (.integer (InitializationBodies.kindCode kind)))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer 0)⟩)
    (hs : heap (p.member "stop") = some ⟨.float64, true, stopOld⟩)
    (hd : heap (p.member "stopDefined") = some ⟨.boolean, true, flagOld⟩) :
    let initialized := finalHeap heap p args
    let exited := InitializationBodies.exitHeap initialized p kind
    (∀ b, (CCalls.machine (CallProofs.linked m)).Behaves
      (.body (.running (Runtime.body m enterSig) (parameters p args) heap) "fmi3Status" .done) b ↔
      b = .terminates ⟨.integer 0, initialized⟩) ∧
    (∀ b, (CCalls.machine (CallProofs.linked m)).Behaves
      (.body (.running (Runtime.body m exitSig) (HistoryBodies.parameters p) initialized)
        "fmi3Status" .done) b ↔ b = .terminates ⟨.integer 0, exited⟩) ∧
    HistoryProofs.Stored exited p (Time.Clock.initial args.start) ∧
    StateProofs.Represents exited p state ∧
    load exited (p.member "mode") =
      some (.integer (nextMode .exitInitialization kind .initialization).code) := by
  obtain ⟨he, hx', hc', _, _, _⟩ :=
    correct m enterSig henter heap p args kind clock state stopOld flagOld ha hc hx hk hm hs hd
  have hframe := frame heap p (p.member "kind") args
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have hk' : load (finalHeap heap p args) (p.member "kind") =
      some (.integer (InitializationBodies.kindCode kind)) := by
    simpa only [load, hframe] using hk
  have hm' : finalHeap heap p args (p.member "mode") =
      some ⟨.int32, true, some (.integer 1)⟩ := by simp [finalHeap]
  exact ⟨he, InitializationBodies.exit_correct m exitSig hexit (finalHeap heap p args) p kind
    (Time.Clock.initial args.start) state hc' hx' hk' hm'⟩
end

end Rumoca.FMI3.InitializationEntry
