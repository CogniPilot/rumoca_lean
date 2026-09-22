import RumocaC.CallPolicyProofs
import RumocaC.CallEvents
import RumocaC.ConcurrentCalls

/-! Certified scheduler-operand checks and call-value invariants for finite sequential and concurrent executions. -/
namespace Rumoca.CCallSites
open CTree CMemory CCalls

/-- Restrictions on actual scheduler operands, including argument syntax.
The complete expression call inventory remains a separate CCallPolicy notion;
nested expression evaluation does not schedule foreign calls in this machine. -/
def Admits (permitted : Indirect.Operand → Prop) (stmt : Stmt) : Prop :=
  (∀ operand, Indirect.operand stmt = some operand → permitted operand) ∧
    match stmt with
    | .branch _ yes no => (∀ child ∈ yes, Admits permitted child) ∧ ∀ child ∈ no, Admits permitted child
    | .whileLoop _ body => ∀ child ∈ body, Admits permitted child
    | _ => True

theorem admits_mono (sound : ∀ operand, p operand → q operand) (stmt : Stmt)
    (admitted : Admits p stmt) : Admits q stmt := by
  induction stmt using Stmt.rec (motive_2 := fun code =>
      (∀ stmt ∈ code, Admits p stmt) → ∀ stmt ∈ code, Admits q stmt) with
  | declare | assign | eval | ret =>
      simp only [Admits] at admitted ⊢
      exact ⟨fun operand extracted => sound operand (admitted.1 operand extracted), trivial⟩
  | branch _ _ _ yes no =>
      simp only [Admits] at admitted ⊢
      exact ⟨fun operand extracted => sound operand (admitted.1 operand extracted),
        yes admitted.2.1, no admitted.2.2⟩
  | whileLoop _ _ body =>
      simp only [Admits] at admitted ⊢
      exact ⟨fun operand extracted => sound operand (admitted.1 operand extracted), body admitted.2⟩
  | nil => rename_i _ _ member; cases member
  | cons stmt rest head tail =>
      rename_i code child member
      rcases List.mem_cons.mp member with rfl | member
      · exact head (code _ List.mem_cons_self)
      · exact tail (fun s hs => code s (List.mem_cons_of_mem stmt hs)) child member

def checkStatement (check : Indirect.Operand → Bool) (stmt : Stmt) : Bool :=
  ((Indirect.operand stmt).map check).getD true &&
    match stmt with
    | .branch _ yes no => yes.attach.all (fun item => checkStatement check item.val) &&
        no.attach.all (fun item => checkStatement check item.val)
    | .whileLoop _ body => body.attach.all (fun item => checkStatement check item.val)
    | _ => true
termination_by sizeOf stmt
decreasing_by
  all_goals simp_wf
  all_goals have bound := List.sizeOf_lt_of_mem item.property
  all_goals omega

def checkFunction (check : Indirect.Operand → Bool) (fn : Function) : Bool := fn.body.all (checkStatement check)

private theorem operand_check (check : Indirect.Operand → Bool) (stmt : Stmt) :
    ((Indirect.operand stmt).map check).getD true = true ↔
      ∀ operand, Indirect.operand stmt = some operand → check operand = true := by
  cases Indirect.operand stmt <;> simp

theorem checkStatement_correct (check : Indirect.Operand → Bool) (stmt : Stmt) :
    checkStatement check stmt = true ↔ Admits (fun operand => check operand = true) stmt := by
  induction stmt using Stmt.rec (motive_2 := fun code =>
      code.all (checkStatement check) = true ↔ ∀ stmt ∈ code, Admits (fun operand => check operand = true) stmt) with
  | declare | assign | eval | ret => simp only [checkStatement, Admits, Bool.and_eq_true, and_true, operand_check]
  | branch _ _ _ hy hn =>
    simp only [checkStatement, Admits, Bool.and_eq_true, List.all_subtype, List.unattach_attach,
      operand_check, hy, hn]
  | whileLoop _ _ hb =>
    simp only [checkStatement, Admits, Bool.and_eq_true, List.all_subtype, List.unattach_attach,
      operand_check, hb]
  | nil => simp
  | cons _ _ hs hc => simp only [List.all_cons, Bool.and_eq_true, List.forall_mem_cons, hs, hc]

theorem checkFunction_correct (check : Indirect.Operand → Bool) (fn : Function) :
    checkFunction check fn = true ↔ ∀ stmt ∈ fn.body, Admits (fun operand => check operand = true) stmt := by
  simp only [checkFunction, List.all_eq_true, checkStatement_correct]

def LoopReady (permitted : Indirect.Operand → Prop) : CLoops.State → Prop
  | .running code _ _ _ => ∀ stmt ∈ code, Admits permitted stmt
  | .returned _ => True

variable [CInterface]

set_option maxHeartbeats 800000 in
theorem loop_ready_next (ready : LoopReady permitted before)
    (step : CLoops.next before = some after) : LoopReady permitted after := by
  unfold CLoops.next CLoops.nextWith at step
  split at step
  all_goals aesop (add simp [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, LoopReady, Admits])

/-- Saved suffixes retain the operand restriction through returns and calls. -/
def Frames (permitted : Indirect.Operand → Prop) : Typed.Continuation → Prop
  | .done => True
  | .caller _ rest _ _ _ outer => (∀ stmt ∈ rest, Admits permitted stmt) ∧ Frames permitted outer

def Ready (permitted : Indirect.Operand → Prop) (calls : String → List Value → Prop) : Typed.State → Prop
  | .body state _ stack => LoopReady permitted state ∧ Frames permitted stack
  | .calling name args _ stack => calls name args ∧ Frames permitted stack
  | .kernel _ _ stack | .returning _ _ stack => Frames permitted stack
  | .halted _ => True

def ProgramAdmits (permitted : Indirect.Operand → Prop) (program : CCalls.Program) : Prop :=
  ∀ name fn, program.definitions name = some (.tree fn) → ∀ stmt ∈ fn.body, Admits permitted stmt

def OperandSound (program : Events.Program E) (permitted : Indirect.Operand → Prop)
    (calls : String → List Value → Prop) : Prop :=
  ∀ operand, permitted operand → ∀ env heap name values,
    Events.resolve program env heap operand.callee = some name →
    arguments env heap operand.args = some values → calls name values

theorem resume_ready (frames : Frames permitted stack)
    (step : Typed.resume value heap stack = some after) : Ready permitted calls after := by
  cases stack with
  | done =>
    simp only [Typed.resume, Typed.resumeWith, Option.some.injEq] at step
    subst after
    trivial
  | caller destination rest env types resultType outer =>
    obtain ⟨code, frames⟩ := frames
    have body : ∀ env types heap, Ready permitted calls
        (.body (.running rest env types heap) resultType outer) := fun _ _ _ => ⟨code, frames⟩
    have returning : ∀ value heap, Ready permitted calls (.returning value heap outer) := fun _ _ => frames
    unfold Typed.resume Typed.resumeWith at step
    split at step
    all_goals
      aesop (add safe apply [body, returning])
        (add simp [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def])

omit [CInterface] in
theorem operand_permitted (ready : Admits permitted stmt)
    (extracted : Indirect.operand stmt = some operand) : permitted operand := by
  cases stmt <;> simp only [Admits] at ready <;> exact ready.1 operand extracted

theorem enter_ready (sound : OperandSound program permitted calls)
    (ready : Ready permitted calls (.body state resultType stack))
    (step : Events.enterCall program state resultType stack = some after) : Ready permitted calls after := by
  obtain ⟨code, frames⟩ := ready
  cases state with
  | returned result => simp [Events.enterCall, Events.enterCallWith] at step
  | running pending env types heap =>
    cases pending with
    | nil =>
      simp only [Events.enterCall, Events.enterCallWith] at step
      split at step
      · cases Option.some.inj step
        exact frames
      · contradiction
    | cons stmt rest =>
      simp only [Events.enterCall, Events.enterCallWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at step
      obtain ⟨operand, extracted, name, resolved, values, evaluated, emitted⟩ := step
      cases Option.some.inj emitted
      exact ⟨sound operand (operand_permitted (code stmt List.mem_cons_self) extracted) env heap name values resolved evaluated,
        fun stmt member => code stmt (List.mem_cons_of_mem _ member), frames⟩

theorem internal_ready (program : Events.Program E)
    (functions : ProgramAdmits permitted program.internal)
    (sound : OperandSound program permitted calls)
    (ready : Ready permitted calls before)
    (step : Events.internalNext program before = some after) : Ready permitted calls after := by
  cases before with
  | body state resultType stack =>
    obtain ⟨code, frames⟩ := ready
    cases state with
    | returned result =>
      simp only [Events.internalNext, Events.internalNextWith, Typed.nextWithExpressions, Option.bind_eq_bind, Option.bind_eq_some_iff] at step
      obtain ⟨value, cast, emitted⟩ := step
      cases Option.some.inj emitted
      exact frames
    | running pending env types heap =>
      simp only [Events.internalNext, Events.internalNextWith, Typed.nextWithExpressions] at step
      cases nextStep : CLoops.next (.running pending env types heap) with
      | none => exact enter_ready sound ⟨code, frames⟩ (by simpa only [nextStep] using step)
      | some nextState =>
        simp only [nextStep, Option.some.injEq] at step
        subst after
        exact ⟨loop_ready_next code nextStep, frames⟩
  | calling name args heap stack =>
    simp only [Events.internalNext, Events.internalNextWith, Typed.nextWithExpressions, Option.bind_eq_bind, Option.bind_eq_some_iff] at step
    obtain ⟨definition, found, entered⟩ := step
    cases definition with
    | tree fn =>
      simp only [Option.bind_eq_some_iff] at entered
      obtain ⟨env, bound, types, typed, emitted⟩ := entered
      cases Option.some.inj emitted
      exact ⟨functions name fn found, ready.2⟩
    | kernel fn =>
      simp only [Option.bind_eq_some_iff] at entered
      obtain ⟨state, entry, emitted⟩ := entered
      cases Option.some.inj emitted
      exact ready.2
  | kernel state heap stack =>
    cases state with
    | returned value =>
      simp only [Events.internalNext, Events.internalNextWith, Typed.nextWithExpressions, Option.some.injEq] at step
      subst after
      exact ready
    | _ =>
      simp only [Events.internalNext, Events.internalNextWith, Typed.nextWithExpressions, Option.bind_eq_bind, Option.bind_eq_some_iff] at step
      obtain ⟨state, moved, emitted⟩ := step
      cases Option.some.inj emitted
      exact ready
  | returning value heap stack => exact resume_ready ready step
  | halted result => simp [Events.internalNext, Events.internalNextWith, Typed.nextWithExpressions] at step

theorem event_ready (program : Events.Program E)
    (functions : ProgramAdmits permitted program.internal) (sound : OperandSound program permitted calls)
    (ready : Ready permitted calls before) (step : Events.Step program before events after) :
    Ready permitted calls after := by
  cases step with
  | internal step => exact internal_ready program functions sound ready step
  | external found converted executed => exact ready.2

theorem reaches_ready (program : Events.Program E)
    (functions : ProgramAdmits permitted program.internal) (sound : OperandSound program permitted calls)
    (ready : Ready permitted calls before)
    (path : Transition.Events.Reaches (Events.machine program).step before events after) :
    Ready permitted calls after := by
  induction path with
  | refl => exact ready
  | next first rest ih => exact ih (event_ready program functions sound ready first)

omit [CInterface] in
theorem ready_withHeap (state : Typed.State) (heap : Heap) :
    Ready permitted calls (Concurrent.withHeap state heap) ↔ Ready permitted calls state := by
  cases state with
  | body state => cases state <;> rfl
  | _ => rfl

def ThreadsReady (permitted : Indirect.Operand → Prop) (calls : String → List Value → Prop)
    (state : Concurrent.State) : Prop :=
  ∀ thread saved, state.threads thread = some saved → Ready permitted calls saved

theorem concurrent_ready (program : Events.Program E)
    (functions : ProgramAdmits permitted program.internal) (sound : OperandSound program permitted calls)
    (ready : ThreadsReady permitted calls before)
    (step : Concurrent.Step program before thread events after) : ThreadsReady permitted calls after := by
  cases step with
  | run found executed =>
    have current := (ready_withHeap _ before.heap).mpr (ready _ _ found)
    have following := event_ready program functions sound current executed
    intro other saved selected
    by_cases same : other = thread
    · subst other
      simp only [Concurrent.update, ↓reduceIte, Option.some.injEq] at selected
      subst saved
      exact (ready_withHeap _ _).mpr following
    · exact ready _ _ (by simpa only [Concurrent.update, if_neg same] using selected)

theorem concurrent_reaches (program : Events.Program E)
    (functions : ProgramAdmits permitted program.internal) (sound : OperandSound program permitted calls)
    (ready : ThreadsReady permitted calls before)
    (path : Transition.Reaches (fun a b => ∃ thread events, Concurrent.Step program a thread events b) before after) :
    ThreadsReady permitted calls after := by
  induction path with
  | refl => exact ready
  | next first rest ih =>
    obtain ⟨thread, events, step⟩ := first
    exact ih (concurrent_ready program functions sound ready step)

end Rumoca.CCallSites

namespace Rumoca.CCallSites
open CTree CMemory CCalls

variable [CInterface]

/-- A named library entry is not also reachable through the imported address
map. This is stronger than merely excluding internal definitions there. -/
def NamedOnly (program : Events.Program E) (name : String) : Prop :=
  ∀ address, program.addresses address ≠ some name

theorem named_resolution (program : Events.Program E) (onlyNamed : NamedOnly program name)
    (resolved : Events.resolve program env heap callee = some name) :
    Indirect.resolve env heap callee = some (.named name) := by
  unfold Events.resolve Events.resolveWith at resolved
  cases found : Indirect.resolveWith CBody.legacyExpressions env heap callee with
  | none => simp [found] at resolved
  | some which =>
    cases which with
    | named actual =>
      simp only [found, Option.bind_eq_bind, Option.bind_some] at resolved
      split at resolved
      · contradiction
      · cases Option.some.inj resolved
        exact found
    | pointer address =>
      exact False.elim (onlyNamed address (by
        simpa only [found, Option.bind_eq_bind, Option.bind_some] using resolved))

end Rumoca.CCallSites
