import RumocaC.CallPolicyExecution

/-! Preserve call ranks through every scheduler step and returning foreign choice. Bound modeled continuation depth for every execution prefix. -/
noncomputable section
namespace Rumoca.CCallDepth
open CTree CMemory CCalls CCallPolicy

/-- Saved callers have strictly increasing ranks outwards. Each suspended
body retains its own rank policy, independent of changing locals and heaps. -/
def Frames (rank : String → Option Nat) (ceiling lower : Nat) : Typed.Continuation → Prop
  | .done => True
  | .caller _ rest _ _ _ outer => ∃ caller, lower ≤ caller ∧ caller ≤ ceiling ∧
      (∀ stmt ∈ rest, StatementAdmits (fun e => rankCallee rank caller e = true) stmt) ∧
      Frames rank ceiling (caller + 1) outer

theorem Frames.weaken (frames : Frames rank ceiling lower stack) (bound : nextLower ≤ lower) :
    Frames rank ceiling nextLower stack := by
  cases stack with
  | done => trivial
  | caller destination rest env types resultType outer =>
      obtain ⟨caller, smaller, upper, ready, frames⟩ := frames
      exact ⟨caller, bound.trans smaller, upper, ready, frames⟩

/-- Counts authored scheduler frames, not native stack bytes or hidden
library/callback implementation frames. -/
def depth : Typed.Continuation → Nat
  | .done => 0
  | .caller _ _ _ _ _ outer => depth outer + 1

theorem Frames.depth_bound (frames : Frames rank ceiling lower stack)
    (range : lower ≤ ceiling + 1) : depth stack + lower ≤ ceiling + 1 := by
  induction stack generalizing lower with
  | done => simpa only [depth, Nat.zero_add] using range
  | caller destination rest env types resultType outer ih =>
      obtain ⟨caller, smaller, upper, _, frames⟩ := frames
      have bound := ih frames (by omega)
      simp only [depth]
      omega

variable [CInterface]

def Ready (rank : String → Option Nat) (ceiling : Nat) (program : Events.Program E) :
    Typed.State → Prop
  | .body state _ stack => ∃ caller, caller ≤ ceiling ∧
      LoopReady (fun e => rankCallee rank caller e = true) state ∧
      Frames rank ceiling (caller + 1) stack
  | .calling name _ _ stack =>
      match program.internal.definitions name with
      | none => Frames rank ceiling 0 stack
      | some _ => ∃ caller, rank name = some caller ∧ caller ≤ ceiling ∧
          Frames rank ceiling (caller + 1) stack
  | .kernel _ _ stack | .returning _ _ stack => Frames rank ceiling 0 stack
  | .halted _ => True

omit [CInterface] in
theorem definition_ready (ranked : ProgramRanked rank program)
    (defined : program.definitions name = some (.tree fn)) (assigned : rank name = some caller) :
    ∀ stmt ∈ fn.body, StatementAdmits (fun e => rankCallee rank caller e = true) stmt := by
  obtain ⟨r, actual, lowers⟩ := ranked name (.tree fn) defined
  have same := Option.some.inj (actual.symm.trans assigned)
  subst r
  intro stmt member
  apply (statement_calls_complete _ stmt).mp
  intro callee occurs
  apply (rank_callee_correct rank caller callee).mpr
  intro target same targetRank targetAssigned
  subst callee
  exact lowers target (List.mem_flatMap.mpr ⟨stmt, member, occurs⟩) targetRank targetAssigned

theorem resume_ready (frames : Frames rank ceiling 0 stack)
    (stepped : Typed.resume value heap stack = some target) : Ready rank ceiling program target := by
  cases stack with
  | done =>
      simp only [Typed.resume, Typed.resumeWith, Option.some.injEq] at stepped
      subst target
      trivial
  | caller destination rest env types resultType outer =>
      obtain ⟨caller, _, upper, ready, frames⟩ := frames
      have body : ∀ env types heap, Ready rank ceiling program
          (.body (.running rest env types heap) resultType outer) :=
        fun _ _ _ => ⟨caller, upper, ready, frames⟩
      have returning : ∀ value heap, Ready rank ceiling program (.returning value heap outer) :=
        fun _ _ => frames.weaken (Nat.zero_le _)
      unfold Typed.resume Typed.resumeWith at stepped
      split at stepped
      all_goals
        aesop (add safe apply [body, returning])
          (add simp [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def])

theorem enter_ready (program : Events.Program E)
    (foreign : CCallPolicy.ForeignAddresses program)
    (ranked : ProgramRanked rank program.internal)
    (ready : Ready rank ceiling program (.body state resultType stack))
    (entered : Events.enterCall program state resultType stack = some target) :
    Ready rank ceiling program target := by
  obtain ⟨caller, upper, policy, frames⟩ := ready
  cases state with
  | returned result => simp [Events.enterCall, Events.enterCallWith] at entered
  | running code env types heap =>
      cases code with
      | nil =>
          simp only [Events.enterCall, Events.enterCallWith] at entered
          split at entered
          · cases Option.some.inj entered
            exact frames.weaken (Nat.zero_le _)
          · contradiction
      | cons stmt rest =>
          simp only [Events.enterCall, Events.enterCallWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at entered
          obtain ⟨operand, extracted, name, resolved, values, converted, emitted⟩ := entered
          cases Option.some.inj emitted
          have suspended : ∀ lower, lower ≤ caller → Frames rank ceiling lower
              (.caller operand.destination rest env types resultType stack) := by
            intro lower smaller
            exact ⟨caller, smaller, upper,
              fun stmt member => policy stmt (List.mem_cons_of_mem _ member), frames⟩
          cases defined : program.internal.definitions name with
          | none =>
              simp only [Ready, defined]
              exact suspended 0 (Nat.zero_le _)
          | some fn =>
              obtain ⟨callee, assigned, _⟩ := ranked name fn defined
              have named := CCallPolicy.internal_resolution program foreign resolved defined
              have permitted := (statement_calls_complete _ stmt).mpr
                (policy stmt List.mem_cons_self) operand.callee (operand_callee stmt operand extracted)
              have designator := named_origin env heap operand.callee named
              have decreases := (rank_callee_correct rank caller operand.callee).mp permitted
                name designator callee assigned
              simp only [Ready, defined]
              exact ⟨callee, assigned, by omega, suspended (callee + 1) (by omega)⟩

end Rumoca.CCallDepth

namespace Rumoca.CCallDepth
open CTree CMemory CCalls CCallPolicy
variable [CInterface]

theorem internal_ready (program : Events.Program E)
    (foreign : CCallPolicy.ForeignAddresses program)
    (ranked : ProgramRanked rank program.internal)
    (ready : Ready rank ceiling program state)
    (stepped : Events.internalNext program state = some target) :
    Ready rank ceiling program target := by
  cases state with
  | body control resultType stack =>
      obtain ⟨caller, upper, policy, frames⟩ := ready
      cases control with
      | returned result =>
          simp only [Events.internalNext, Events.internalNextWith, Typed.nextWithExpressions, Option.bind_eq_bind,
            Option.bind_eq_some_iff] at stepped
          obtain ⟨value, converted, emitted⟩ := stepped
          cases Option.some.inj emitted
          exact frames.weaken (Nat.zero_le _)
      | running code env types heap =>
          simp only [Events.internalNext, Events.internalNextWith, Typed.nextWithExpressions] at stepped
          cases next : CLoops.next (.running code env types heap) with
          | none =>
              simp only [next] at stepped
              exact enter_ready program foreign ranked ⟨caller, upper, policy, frames⟩ stepped
          | some following =>
              simp only [next, Option.some.injEq] at stepped
              subst target
              exact ⟨caller, upper, loop_ready_next policy next, frames⟩
  | calling name args heap stack =>
      simp only [Events.internalNext, Events.internalNextWith, Typed.nextWithExpressions, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at stepped
      obtain ⟨definition, defined, entered⟩ := stepped
      simp only [Ready, defined] at ready
      obtain ⟨caller, assigned, upper, frames⟩ := ready
      cases definition with
      | tree fn =>
          simp only [Option.bind_eq_some_iff] at entered
          obtain ⟨env, parameters, types, typed, emitted⟩ := entered
          cases Option.some.inj emitted
          exact ⟨caller, upper, definition_ready ranked defined assigned, frames⟩
      | kernel fn =>
          simp only [Option.bind_eq_some_iff] at entered
          obtain ⟨control, entry, emitted⟩ := entered
          cases Option.some.inj emitted
          exact frames.weaken (Nat.zero_le _)
  | kernel control heap stack =>
      cases control with
      | returned value =>
          simp only [Events.internalNext, Events.internalNextWith, Typed.nextWithExpressions, Option.some.injEq] at stepped
          subst target
          exact ready
      | entry | running =>
          simp only [Events.internalNext, Events.internalNextWith, Typed.nextWithExpressions, Option.bind_eq_bind,
            Option.bind_eq_some_iff] at stepped
          obtain ⟨following, next, emitted⟩ := stepped
          cases Option.some.inj emitted
          exact ready
  | returning value heap stack =>
      exact resume_ready ready (by simpa only [Events.internalNext, Events.internalNextWith, Typed.nextWithExpressions] using stepped)
  | halted result => simp [Events.internalNext, Events.internalNextWith, Typed.nextWithExpressions] at stepped

theorem event_ready (program : Events.Program E)
    (foreign : CCallPolicy.ForeignAddresses program)
    (ranked : ProgramRanked rank program.internal)
    (ready : Ready rank ceiling program state)
    (stepped : Events.Step program state events target) :
    Ready rank ceiling program target := by
  cases stepped with
  | internal step => exact internal_ready program foreign ranked ready step
  | external found converted executed =>
      simpa only [Ready, program.disjoint _ _ found] using ready

theorem reaches_ready (program : Events.Program E)
    (foreign : CCallPolicy.ForeignAddresses program)
    (ranked : ProgramRanked rank program.internal)
    (ready : Ready rank ceiling program state)
    (path : Transition.Events.Reaches (Events.machine program).step state events target) :
    Ready rank ceiling program target := by
  induction path with
  | refl => exact ready
  | next first rest ih => exact ih (event_ready program foreign ranked ready first)

def stateDepth : Typed.State → Nat
  | .body _ _ stack | .calling _ _ _ stack | .kernel _ _ stack | .returning _ _ stack => depth stack
  | .halted _ => 0

theorem ready_depth (ready : Ready rank ceiling program state) : stateDepth state ≤ ceiling + 1 := by
  cases state with
  | body control resultType stack =>
      obtain ⟨caller, upper, _, frames⟩ := ready
      have bound := frames.depth_bound (by omega)
      simp only [stateDepth]
      omega
  | calling name args heap stack =>
      cases defined : program.internal.definitions name with
      | none =>
          simp only [Ready, defined] at ready
          simpa only [stateDepth, Nat.add_zero] using ready.depth_bound (Nat.zero_le _)
      | some fn =>
          simp only [Ready, defined] at ready
          obtain ⟨caller, _, upper, frames⟩ := ready
          have bound := frames.depth_bound (by omega)
          simp only [stateDepth]
          omega
  | kernel control heap stack | returning value heap stack =>
      simpa only [stateDepth, Nat.add_zero] using ready.depth_bound (Nat.zero_le _)
  | halted result => exact Nat.zero_le _

theorem initial_ready (program : Events.Program E) (ranked : ProgramRanked rank program.internal)
    (bound : ∀ r, rank name = some r → r ≤ ceiling) :
    Ready rank ceiling program (.calling name args heap .done) := by
  cases defined : program.internal.definitions name with
  | none => simp [Ready, defined, Frames]
  | some fn =>
      obtain ⟨caller, assigned, _⟩ := ranked name fn defined
      simp only [Ready, defined]
      exact ⟨caller, assigned, bound caller assigned, trivial⟩

/-- Every finite execution prefix retains the bound, including prefixes of
stuck or nonterminating executions and arbitrary returning foreign choices.
This is not a native stack-byte or foreign implementation bound. -/
theorem execution_depth_bound (program : Events.Program E)
    (foreign : CCallPolicy.ForeignAddresses program)
    (ranked : ProgramRanked rank program.internal)
    (bound : ∀ r, rank name = some r → r ≤ ceiling)
    (path : Transition.Events.Reaches (Events.machine program).step
      (.calling name args heap .done) events target) :
    stateDepth target ≤ ceiling + 1 :=
  ready_depth (reaches_ready program foreign ranked (initial_ready program ranked bound) path)

end Rumoca.CCallDepth
