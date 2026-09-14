import RumocaFMI3.MENumericalRestart
import RumocaFMI3.MENumericalAtomic
import RumocaFMI3.InitializationEnvironment

noncomputable section
namespace Rumoca.FMI3.MENumericalRun
open CTree CMemory StaticFactory

inductive Action where
  | numerical (action : MENumericalHistory.Action)
  | restart (args : Initialization.Arguments)

inductive ReferenceTrace : MENumericalHistory.ReferenceState → List Action →
    MENumericalHistory.ReferenceState → Prop where
  | nil : ReferenceTrace reference [] reference
  | numerical : action.Allowed reference → ReferenceTrace (action.next reference) rest final →
      ReferenceTrace reference (.numerical action :: rest) final
  | restart : args.Admissible → ReferenceTrace (.restart args) rest final →
      ReferenceTrace reference (.restart args :: rest) final

def observations (model : Solve.FMI3Model source) (reference : MENumericalHistory.ReferenceState) :
    List Action → List (Option Value)
  | [] => []
  | .numerical action :: rest => action.expected model reference :: observations model (action.next reference) rest
  | .restart args :: rest => none :: none :: none :: observations model (.restart args) rest

/-- Each restart checkpoint records the actual heap after exiting initialization.
This permits source initialization to be stated before later trial-state writes. -/
abbrev Epoch := Initialization.Arguments × Heap

/-- Actual scripts expose each reset/entry/exit status and every query result.
Intermediate heaps and initialized checkpoints come from target execution. -/
inductive Executed [CInterface] (program : CCalls.Events.Program E)
    (p : Address) (addresses : String → Address) (buffer : Address) :
    Heap → List Action → List (MENumericalHistory.Observation E) → Heap → List Epoch → Prop where
  | nil : Executed program p addresses buffer heap [] [] heap []
  | numerical : MENumericalHistory.Executed program p addresses buffer heap [action] [value] middle →
      Executed program p addresses buffer middle rest values final epochs →
      Executed program p addresses buffer heap (.numerical action :: rest) (value :: values) final epochs
  | restart :
      (CCalls.Events.machine program).Behaves
        (.calling Reset.signature.name [.pointer (some p)] heap .done) (.terminates resetEvents ⟨resetStatus, resetHeap⟩) →
      (CCalls.Events.machine program).Behaves
        (.calling InitializationCalls.signature.name
          (InitializationCalls.arguments (some p) (InitializationCalls.Raw.ofFinite args)) resetHeap .done)
        (.terminates enterEvents ⟨enterStatus, enteredHeap⟩) →
      (CCalls.Events.machine program).Behaves
        (.calling InitializationExit.signature.name (InitializationExit.arguments (some p)) enteredHeap .done)
        (.terminates exitEvents ⟨exitStatus, exitedHeap⟩) →
      Executed program p addresses buffer exitedHeap rest values final epochs →
      Executed program p addresses buffer heap (.restart args :: rest)
        (⟨resetEvents, resetStatus, none⟩ :: ⟨enterEvents, enterStatus, none⟩ ::
          ⟨exitEvents, exitStatus, none⟩ :: values) final ((args, exitedHeap) :: epochs)

/-- The derived certificate contains complete calls, not just successful
executions, and records all reset initialization checkpoints. -/
inductive Calls [CInterface] (program : CCalls.Events.Program E)
    (p : Address) (addresses : String → Address) (buffer : Address) :
    Heap → List Action → List (Option Value) → Heap → List Epoch → Prop where
  | nil : Calls program p addresses buffer heap [] [] heap []
  | numerical : MENumericalHistory.Calls program p addresses buffer heap [action] [value] middle →
      Calls program p addresses buffer middle rest values final epochs →
      Calls program p addresses buffer heap (.numerical action :: rest) (value :: values) final epochs
  | restart :
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling Reset.signature.name [.pointer (some p)] heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, Reset.finalHeap heap p⟩) →
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling InitializationCalls.signature.name
          (InitializationCalls.arguments (some p) (InitializationCalls.Raw.ofFinite args)) (Reset.finalHeap heap p) .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, InitializationEntry.finalHeap (Reset.finalHeap heap p) p args⟩) →
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling InitializationExit.signature.name (InitializationExit.arguments (some p))
          (InitializationEntry.finalHeap (Reset.finalHeap heap p) p args) .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, MENumericalHistory.restarted heap p args⟩) →
      Calls program p addresses buffer (MENumericalHistory.restarted heap p args) rest values final epochs →
      Calls program p addresses buffer heap (.restart args :: rest)
        (none :: none :: none :: values) final ((args, MENumericalHistory.restarted heap p args) :: epochs)

theorem Calls.executes [CInterface] {program : CCalls.Events.Program E}
    (certified : Calls program p addresses buffer heap actions values after epochs) :
    Executed program p addresses buffer heap actions (values.map MENumericalHistory.Observation.ok) after epochs := by
  induction certified with
  | nil => exact .nil
  | numerical called _ ih => exact .numerical called.executes ih
  | restart reset enter exit _ ih =>
    exact .restart ((reset _).mpr rfl) ((enter _).mpr rfl) ((exit _).mpr rfl) ih

theorem Calls.determines [CInterface] {program : CCalls.Events.Program E}
    (certified : Calls program p addresses buffer heap actions values final epochs)
    (executed : Executed program p addresses buffer heap actions observed after actualEpochs) :
    observed = values.map MENumericalHistory.Observation.ok ∧ after = final ∧ actualEpochs = epochs := by
  induction executed generalizing values final epochs with
  | nil => cases certified; exact ⟨rfl, rfl, rfl⟩
  | numerical called _ ih =>
    cases certified with
    | numerical expected following =>
      obtain ⟨sameValues, sameHeap⟩ := expected.determines called
      cases sameHeap
      have sameValue := (List.cons.inj sameValues).1
      obtain ⟨tail, finish, checkpoints⟩ := ih following
      exact ⟨by simp only [List.map_cons, sameValue, tail], finish, checkpoints⟩
  | restart reset enter exit _ ih =>
    cases certified with
    | restart resetExpected enterExpected exitExpected following =>
      have resetSame := (resetExpected _).mp reset
      cases resetSame
      have enterSame := (enterExpected _).mp enter
      cases enterSame
      have exitSame := (exitExpected _).mp exit
      cases exitSame
      obtain ⟨tail, finish, checkpoints⟩ := ih following
      exact ⟨by simp only [List.map_cons, MENumericalHistory.Observation.ok, tail],
        finish, by rw [checkpoints]⟩

def Outside (p : Address) (addresses : String → Address) (buffer q : Address) : Prop :=
  MENumericalHistory.Outside p addresses buffer q ∧ q ≠ p.member "stop" ∧ q ≠ p.member "stopDefined"

theorem restart_frame (heap : Heap) (p : Address) (args : Initialization.Arguments)
    (outside : Outside p addresses buffer q) : MENumericalHistory.restarted heap p args q = heap q := by
  obtain ⟨⟨⟨time, mode, event, minimum, completed, _⟩, state, _⟩, stop, stopDefined⟩ := outside
  exact (InitializationCalls.exited_frame _ p q args .me time minimum event completed stop stopDefined mode).trans
    (Reset.frame heap p q state time minimum event completed stop stopDefined mode)

theorem trace (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E),
      MEEnvironment.Quiet model program → StaticReset.ExecutionContract program →
      program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) →
      program.internal.definitions InitializationExit.signature.name = some (.tree (Runtime.function model InitializationExit.signature)) →
      ∀ (heap : Heap) (p : Address) (clock : Time.Clock)
        (reference final : MENumericalHistory.ReferenceState) (addresses : String → Address)
        (buffer : Address) (actions : List Action),
      MENumericalHistory.Stored heap p clock reference addresses buffer → Reset.Storage heap p →
      ReferenceTrace reference actions final →
      ∃ after finalClock epochs,
        Calls program p addresses buffer heap actions (observations model reference actions) after epochs ∧
        MENumericalHistory.Stored after p finalClock final addresses buffer ∧ Reset.Storage after p ∧
        CReadOnly.Preserves heap after ∧ CAtomicBoolean.Preserves heap after ∧
        (∀ q, Outside p addresses buffer q → after q = heap q) := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program quiet reset enterDefined exitDefined heap p clock reference final addresses buffer actions stored storage admitted
  induction admitted generalizing heap clock with
  | nil => exact ⟨heap, clock, [], .nil, stored, storage, .refl heap, .refl heap, fun _ _ => rfl⟩
  | numerical accepted _ ih =>
    obtain ⟨prepared, called, nextStored, output, controls, readonly, frame⟩ :=
      MENumericalHistory.step program quiet stored _ accepted
    have nextReset := MENumericalHistory.step_reset_storage model _ stored nextStored storage
    obtain ⟨after, finalClock, epochs, rest, finalStored, finalReset, restReadonly, restAtomic, restFrame⟩ := ih _ _ nextStored nextReset
    exact ⟨after, finalClock, epochs, .numerical (.cons prepared called output controls .nil) rest,
      finalStored, finalReset, readonly.trans restReadonly,
      (MENumericalHistory.action_atomic model stored _).trans restAtomic,
      fun q outside => (restFrame q outside).trans (frame q outside.1)⟩
  | restart admissible _ ih =>
    have resetCall := reset.successful heap p .me _ storage stored.control.kind stored.mode_loaded
    obtain ⟨enterCall, exitCall⟩ := InitializationEnvironment.calls header objects literals model
      program (Reset.finalHeap heap p) p _ .me enterDefined exitDefined admissible
      (StaticReset.entry_storage heap p) ((StaticReset.kind_value heap p).trans stored.control.kind)
    have nextStored := stored.restart _ admissible
    obtain ⟨after, finalClock, epochs, rest, finalStored, finalReset, restReadonly, restAtomic, restFrame⟩ :=
      ih _ _ nextStored (MENumericalHistory.initialized_reset_storage (Reset.finalHeap heap p) p _
        Binary64.positiveZero (MENumericalHistory.reset_state_cell heap p))
    exact ⟨after, finalClock, _, .restart resetCall enterCall exitCall rest,
      finalStored, finalReset,
      (CCalls.Events.termination_preserves ((resetCall _).mpr rfl)).trans
        ((CCalls.Events.termination_preserves ((enterCall _).mpr rfl)).trans
          ((CCalls.Events.termination_preserves ((exitCall _).mpr rfl)).trans restReadonly)),
      (MENumericalHistory.restart_atomic storage _).trans restAtomic,
      fun q outside => (restFrame q outside).trans (restart_frame heap p _ outside)⟩

theorem ReferenceTrace.live (admitted : ReferenceTrace reference actions final)
    (live : reference.control.Live) : final.control.Live := by
  induction admitted with
  | nil => exact live
  | numerical _ _ ih => exact ih (MENumericalHistory.Action.next_live _ live)
  | restart _ _ ih => exact ih (Or.inl rfl)

end Rumoca.FMI3.MENumericalRun
end
