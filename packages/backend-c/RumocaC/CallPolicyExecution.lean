import RumocaC.CallPolicyProofs
import RumocaC.CallEvents

/-! Connect ranked call inventories to actual eventful call resolution. Imported-address obligations remain explicit. -/
noncomputable section
namespace Rumoca.CCallPolicy
open CTree CMemory CCalls
variable [CInterface]

/-- The address table may bind imported functions, but not generated internal
entries. This is an explicit linker condition, not an assumption that an
identifier is necessarily a direct call. -/
def ForeignAddresses (program : Events.Program E) : Prop :=
  ∀ address name, program.addresses address = some name →
    program.internal.definitions name = none

theorem internal_resolution (program : Events.Program E)
    (foreign : ForeignAddresses program)
    (resolved : Events.resolve program env heap callee = some name)
    (target : program.internal.definitions name = some definition) :
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
          have bound : program.addresses address = some name := by
            simpa only [found, Option.bind_eq_bind, Option.bind_some] using resolved
          have absent := foreign address name bound
          rw [absent] at target
          contradiction

/-- Internal calls entered by the shared eventful resolver use an edge of
the complete source function inventory, even when other calls are indirect. -/
theorem entered_internal_edge (program : Events.Program E)
    (foreign : ForeignAddresses program) (fn : Function)
    (defined : program.internal.definitions caller = some (.tree fn))
    (ready : LoopReady (fun e => e ∈ fn.body.flatMap statementCalls) state)
    (entered : Events.enterCall program state resultType stack =
      some (.calling name args after later))
    (target : program.internal.definitions name = some definition) :
    ProgramEdge program.internal caller name := by
  cases state with
  | returned result => simp [Events.enterCall, Events.enterCallWith] at entered
  | running code env types heap =>
      cases code with
      | nil =>
          simp only [Events.enterCall, Events.enterCallWith] at entered
          split at entered <;> simp at entered
      | cons stmt rest =>
          simp only [Events.enterCall, Events.enterCallWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at entered
          obtain ⟨operand, extracted, resolvedName, resolved, values, converted, emitted⟩ := entered
          have names := (Typed.State.calling.inj (Option.some.inj emitted)).1
          rw [names] at resolved
          exact resolved_named_edge program.internal fn defined ready extracted
            (internal_resolution program foreign resolved target) target

/-- A scheduled internal call from a body is the corresponding inventory
edge. Ordinary loop steps cannot invent a call; numerical leaves are handled
by the separately checked kernel_no_call theorem. -/
theorem scheduled_internal_edge (program : Events.Program E)
    (foreign : ForeignAddresses program) (fn : Function)
    (defined : program.internal.definitions caller = some (.tree fn))
    (ready : LoopReady (fun e => e ∈ fn.body.flatMap statementCalls) state)
    (stepped : Events.internalNext program (.body state resultType stack) =
      some (.calling name args after later))
    (target : program.internal.definitions name = some definition) :
    ProgramEdge program.internal caller name := by
  cases state with
  | returned result =>
      simp [Events.internalNext, Events.internalNextWith, Typed.nextWithExpressions, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at stepped
  | running code env types heap =>
      simp only [Events.internalNext, Events.internalNextWith, Typed.nextWithExpressions] at stepped
      cases next : CLoops.next (.running code env types heap) with
      | some following => simp [next] at stepped
      | none =>
          simp only [next] at stepped
          exact entered_internal_edge program foreign fn defined ready stepped target

/-- Every generated call actually scheduled from a policy-preserving body
strictly decreases the same rank used by the source-bound artifact theorem. -/
theorem scheduled_internal_decreases (program : Events.Program E)
    (foreign : ForeignAddresses program) (ranked : ProgramRanked rank program.internal)
    (fn : Function) (defined : program.internal.definitions caller = some (.tree fn))
    (ready : LoopReady (fun e => e ∈ fn.body.flatMap statementCalls) state)
    (stepped : Events.internalNext program (.body state resultType stack) =
      some (.calling name args after later))
    (target : program.internal.definitions name = some definition) :
    (rank name).getD 0 < (rank caller).getD 0 :=
  program_edge_decreases ranked
    (scheduled_internal_edge program foreign fn defined ready stepped target)

end Rumoca.CCallPolicy
