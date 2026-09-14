import RumocaFMI3.CSRunTransition

noncomputable section
namespace Rumoca.FMI3.CSRun
open CTree CMemory CBody StaticFactory CCalls

/-- Returned public actions, specified solely by the actual C machine.
Reset/reinitialization retains all three calls and their intermediate heaps.
All return codes are arbitrary here; the action contract establishes success.
The script's restart result is the final exit-initialization return code. -/
inductive Performed [CInterface] (program : Events.Program E) (p : Address) :
    Heap → Action → Int → List E → Heap → Prop where
  | step : (Events.machine program).Behaves
      (.calling StepEntry.signature.name (StepEntry.arguments (some p) request.point request.step request.flag outputs) heap .done)
      (.terminates events ⟨.integer status, after⟩) →
      Performed program p heap (.step request outputs) status events after
  | restart {heap resetHeap enteredHeap after : Heap} {args : Initialization.Arguments} :
      (Events.machine program).Behaves (.calling Reset.signature.name [.pointer (some p)] heap .done)
        (.terminates resetEvents ⟨.integer resetStatus, resetHeap⟩) →
      (Events.machine program).Behaves
        (.calling InitializationCalls.signature.name
          (InitializationCalls.arguments (some p) (InitializationCalls.Raw.ofFinite args)) resetHeap .done)
        (.terminates enterEvents ⟨.integer enterStatus, enteredHeap⟩) →
      (Events.machine program).Behaves
        (.calling InitializationExit.signature.name (InitializationExit.arguments (some p)) enteredHeap .done)
        (.terminates exitEvents ⟨.integer exitStatus, after⟩) →
      Performed program p heap (.restart args) exitStatus (resetEvents ++ enterEvents ++ exitEvents) after

/-- A completed host script records actual target calls, statuses and callback
invocations. Its definition contains no source/Solve invariant or certificate. -/
inductive Completed [CInterface] (program : Events.Program E) (p : Address) :
    Heap → List Action → List Int → List E → Heap → Prop where
  | nil : Completed program p heap [] [] [] heap
  | cons : Performed program p heap action status events middle →
      Completed program p middle rest statuses later after →
      Completed program p heap (action :: rest) (status :: statuses) (events ++ later) after

/-- An actual blocked call, retaining any completed calls within a restart.
No reference status, heap invariant or callback-return premise occurs here. -/
inductive Faulted [CInterface] (program : Events.Program E) (p : Address) : Heap → Action → Prop where
  | step : (Events.machine program).Behaves
      (.calling StepEntry.signature.name
        (StepEntry.arguments (some p) request.point request.step request.flag outputs) heap .done) (.wrong []) →
      Faulted program p heap (.step request outputs)
  | reset : (Events.machine program).Behaves (.calling Reset.signature.name [.pointer (some p)] heap .done) (.wrong []) →
      Faulted program p heap (.restart args)
  | enter :
      (Events.machine program).Behaves (.calling Reset.signature.name [.pointer (some p)] heap .done)
        (.terminates events ⟨status, resetHeap⟩) →
      (Events.machine program).Behaves
        (.calling InitializationCalls.signature.name
          (InitializationCalls.arguments (some p) (InitializationCalls.Raw.ofFinite args)) resetHeap .done) (.wrong []) →
      Faulted program p heap (.restart args)
  | exit :
      (Events.machine program).Behaves (.calling Reset.signature.name [.pointer (some p)] heap .done)
        (.terminates resetEvents ⟨resetStatus, resetHeap⟩) →
      (Events.machine program).Behaves
        (.calling InitializationCalls.signature.name
          (InitializationCalls.arguments (some p) (InitializationCalls.Raw.ofFinite args)) resetHeap .done)
        (.terminates enterEvents ⟨enterStatus, enteredHeap⟩) →
      (Events.machine program).Behaves
        (.calling InitializationExit.signature.name (InitializationExit.arguments (some p)) enteredHeap .done) (.wrong []) →
      Faulted program p heap (.restart args)

/-- A finite host script can stop at a real call after an actual returned
prefix. This relation does not assume that an external logger returns. -/
inductive Stopped [CInterface] (program : Events.Program E) (p : Address) : Heap → List Action → Prop where
  | here : Faulted program p heap action → Stopped program p heap (action :: rest)
  | later : Performed program p heap action status events middle →
      Stopped program p middle rest → Stopped program p heap (action :: rest)

theorem Executed.performed [CInterface] {program : Events.Program E}
    (executed : Executed program p heap action after status) :
    Performed program p heap action status [] after := by
  cases executed with
  | step called => exact .step ((called _).mpr rfl)
  | restart reset enter leave => exact .restart ((reset _).mpr rfl) ((enter _).mpr rfl) ((leave _).mpr rfl)

end Rumoca.FMI3.CSRun
end
