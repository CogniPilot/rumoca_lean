import RumocaC.CallSites
import RumocaC.TypedEventsTransfer

/-! A syntax invariant for the ordinary void-call machine. It discharges the
reachable-state resolution premise of the event transfer from the actual
function bodies and constant namespace, without restricting callback heaps. -/
noncomputable section
namespace Rumoca.CCallSites.LoopCalls
open CTree CMemory CCalls

def Frames (permitted : Indirect.Operand → Prop) : CLoops.Calls.Continuation → Prop
  | .done => True
  | .caller rest _ _ outer => (∀ stmt ∈ rest, Admits permitted stmt) ∧ Frames permitted outer

def Ready (permitted : Indirect.Operand → Prop) : CLoops.Calls.State → Prop
  | .body state stack => LoopReady permitted state ∧ Frames permitted stack
  | .calling _ _ _ stack | .returning _ stack => Frames permitted stack
  | .halted _ => True

def DefinitionsAdmit (permitted : Indirect.Operand → Prop)
    (definitions : CLoops.Calls.Definitions) : Prop :=
  ∀ name fn, definitions name = some fn → ∀ stmt ∈ fn.body, Admits permitted stmt

variable [interface : CInterface]

theorem enter_ready (ready : Ready permitted (.body state stack))
    (step : CLoops.Calls.enterCall state stack = some after) : Ready permitted after := by
  obtain ⟨code, frames⟩ := ready
  unfold CLoops.Calls.enterCall at step
  split at step
  · rename_i name args rest env types heap
    have tail : ∀ stmt ∈ rest, Admits permitted stmt :=
      fun stmt member => code stmt (List.mem_cons_of_mem _ member)
    split at step
    · cases step
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at step
      obtain ⟨values, _, step⟩ := step
      cases step
      exact ⟨tail, frames⟩
  · cases step

theorem ready_next (admitted : DefinitionsAdmit permitted definitions)
    (ready : Ready permitted before)
    (step : CLoops.Calls.next definitions before = some after) : Ready permitted after := by
  cases before with
  | halted => cases step
  | returning heap stack =>
    cases stack <;> simp only [CLoops.Calls.next, Option.some.injEq] at step <;> subst after
    · trivial
    · exact ready
  | calling name args heap stack =>
    simp only [CLoops.Calls.next, Option.bind_eq_bind, Option.bind_eq_some_iff] at step
    obtain ⟨fn, found, step⟩ := step
    split at step
    · cases step
    · simp only [Option.bind_eq_some_iff, Option.pure_def] at step
      obtain ⟨env, _, types, _, step⟩ := step
      cases step
      exact ⟨admitted name fn found, ready⟩
  | body state stack =>
    cases state with
    | returned result =>
      simp only [CLoops.Calls.next] at step
      split at step
      · cases step
        exact ready.2
      · cases step
    | running code env types heap =>
      cases ordinary : CLoops.next (.running code env types heap) with
      | some following =>
        simp only [CLoops.Calls.next, ordinary, Option.some.injEq] at step
        subst after
        exact ⟨loop_ready_next ready.1 ordinary, ready.2⟩
      | none =>
        simp only [CLoops.Calls.next, ordinary] at step
        exact enter_ready ready step

theorem ready_reaches (admitted : DefinitionsAdmit permitted definitions)
    (ready : Ready permitted before)
    (ran : Transition.Reaches (CLoops.Calls.machine definitions).step before after) :
    Ready permitted after := by
  induction ran with
  | refl => exact ready
  | next step _ ih => exact ih (ready_next admitted ready step)

/-- Only direct identifier operands matter for the void loop scheduler. Other
operand forms are not thereby proved executable. -/
def DirectNames (allowed : String → Prop) (operand : Indirect.Operand) : Prop :=
  ∀ name, operand.callee = .id name → allowed name

theorem ready_resolves (program : Events.Program E)
    (clear : ∀ name, allowed name → interface.constants name = none ∧ name ≠ "isfinite")
    (ready : Ready (DirectNames allowed) state) : Events.Resolves program state := by
  cases state with
  | calling | returning | halted => trivial
  | body state stack =>
    cases state with
    | returned => trivial
    | running code env types heap =>
      cases code with
      | nil => trivial
      | cons stmt rest =>
        cases stmt with
        | eval expr =>
          cases expr with
          | call callee args =>
            cases callee with
            | id name =>
              have admitted := ready.1 _ (List.mem_cons_self)
              have permitted := operand_permitted admitted
                (show Indirect.operand (.eval (.call (.id name) args)) =
                  some ⟨.discard, .id name, args⟩ from rfl)
              have named := clear name (permitted name rfl)
              intro absent
              have unshadowed : env name = none := by
                cases value : env name <;> simp_all
              have resolved : Indirect.resolve env heap (.id name) = some (.named name) :=
                Indirect.named_iff.mpr ⟨unshadowed, named.1⟩
              simp [Events.resolve, resolved, named.2]
            | _ => trivial
          | _ => trivial
        | _ => trivial

theorem reachable_resolves (program : Events.Program E)
    (admitted : DefinitionsAdmit (DirectNames allowed) definitions)
    (clear : ∀ name, allowed name → interface.constants name = none ∧ name ≠ "isfinite")
    (ready : Ready (DirectNames allowed) initial) :
    ∀ state, Transition.Reaches (CLoops.Calls.machine definitions).step initial state →
      Events.Resolves program state :=
  fun _ ran => ready_resolves program clear (ready_reaches admitted ready ran)

/-- A closed numerical call has no caller suffix to certify. Its internal
calls resolve from the actual definition-body inventory and constant names. -/
theorem call_resolves (program : Events.Program E)
    (admitted : DefinitionsAdmit (DirectNames allowed) definitions)
    (clear : ∀ name, allowed name → interface.constants name = none ∧ name ≠ "isfinite")
    (name : String) (args : List Value) (heap : Heap) :
    ∀ state, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling name args heap .done) state → Events.Resolves program state :=
  reachable_resolves program admitted clear True.intro

theorem call_terminates_events (program : Events.Program E)
    (linked : Typed.Extends definitions program.internal)
    (admitted : DefinitionsAdmit (DirectNames allowed) definitions)
    (clear : ∀ name, allowed name → interface.constants name = none ∧ name ≠ "isfinite")
    (name : String) (args : List Value) (heap finalHeap : Heap)
    (ran : (CLoops.Calls.machine definitions).Behaves
      (.calling name args heap .done) (.terminates finalHeap)) :
    Transition.Reaches (fun a b => Events.internalNext program a = some b)
      (.calling name args heap .done) (.halted ⟨.void, finalHeap⟩) :=
  Events.loop_terminates_reaches_events program definitions linked ran
    (call_resolves program admitted clear name args heap)

end Rumoca.CCallSites.LoopCalls
