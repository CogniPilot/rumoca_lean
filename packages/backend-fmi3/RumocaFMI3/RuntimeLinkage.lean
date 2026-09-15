import RumocaC.CallLinkage
import RumocaC.CallDepth
import RumocaFMI3.CallPolicy
import RumocaFMI3.StaticRuntimeLinkage
import RumocaFMI3.LoggingCapability
import RumocaC.MathCalls

/-! One prepared generated/library/logger environment, with proved call-depth bounds. Native library and callback internals are outside the modeled stack. -/
noncomputable section
namespace Rumoca.FMI3.RuntimeLinkage
open CTree CMemory CCalls CCalls.Events CCallPolicy CallPolicy

theorem unranked_undefined (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) (unranked : functionRank name = none) :
    (LiteralPreparation.program model sigs).definitions name = none := by
  cases found : (LiteralPreparation.program model sigs).definitions name with
  | none => rfl
  | some fn =>
      obtain ⟨r, assigned, _⟩ := program_rank model sigs covered name fn found
      rw [unranked] at assigned
      contradiction

theorem static_unranked (member : name ∈ StaticRuntime.routineNames) : functionRank name = none := by
  simp only [StaticRuntime.routineNames, CStringCalls.routineNames,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem static_fresh (covered : PublicAPI.Covered sigs) : StaticRuntime.ExternalNamesFresh sigs := by
  intro sig member routine
  have assigned := covered_ranks covered sig member
  rw [static_unranked routine] at assigned
  contradiction

variable [interface : CInterface]

/-- One consistent environment supplies the exact generated table, all five
static-runtime routines, floor, and every int32 rounding observation. -/
def linked (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32)
    (double : interface.types "double" = some .float64)
    (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31) : Events.Program E :=
  let base := StaticRuntime.linked model sigs (static_fresh covered) tag boolean size integer
  let math := Linkage.withExternal base (CMathCalls.floorExternal double)
    (unranked_undefined model sigs covered (by change functionRank "floor" = none; decide +kernel)) rfl
  Linkage.withExternal math (CMathCalls.roundingExternal integer observed range)
    (unranked_undefined model sigs covered (by change functionRank "fegetround" = none; decide +kernel)) rfl

theorem linked_contract (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32)
    (double : interface.types "double" = some .float64)
    (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31) :
    let program := linked model sigs covered tag boolean size integer double observed range
    program.internal = LiteralPreparation.program model sigs ∧
    CCallPolicy.ForeignAddresses program ∧
    ProgramRanked functionRank program.internal ∧
    (∀ name fn, StaticRuntime.library tag boolean size integer name = some fn →
      program.externals name = some fn) ∧
    program.externals "floor" = some (CMathCalls.floorExternal double) ∧
    program.externals "fegetround" = some (CMathCalls.roundingExternal integer observed range) := by
  dsimp only
  refine ⟨rfl, ?_, program_rank model sigs covered, ?_, rfl, rfl⟩
  · intro address name found
    contradiction
  · intro name fn found
    exact Linkage.withExternal_keeps _ _
      (unranked_undefined model sigs covered (by change functionRank "fegetround" = none; decide +kernel)) rfl
      (Linkage.withExternal_keeps _ _
        (unranked_undefined model sigs covered (by change functionRank "floor" = none; decide +kernel)) rfl found)

end Rumoca.FMI3.RuntimeLinkage

namespace Rumoca.FMI3.RuntimeLinkage
open CTree CMemory CCalls CCalls.Events CCallPolicy CallPolicy
variable [interface : CInterface]

/-- Register an importer callback without replacing any existing function
or address binding. Its returning effects and possible lack of a return are
supplied by the importer relation, not invented by the linker. -/
def withLogger (program : Events.Program Invocation) (logger : Address)
    (name : String) (effect : ReturningEffect (Logging.signature name))
    (internalFree : program.internal.definitions name = none)
    (externalFree : program.externals name = none)
    (addressFree : program.addresses logger = none) : Events.Program Invocation :=
  let extended := Linkage.withExternal program
    (External.observed (Logging.signature name) effect) internalFree externalFree
  Linkage.withAddress extended logger name addressFree
    ⟨_, Linkage.withExternal_bound program (External.observed (Logging.signature name) effect) internalFree externalFree⟩

theorem withLogger_contract (program : Events.Program Invocation) (logger : Address)
    (environment : Option Address) (name : String) (effect : ReturningEffect (Logging.signature name))
    (internalFree : program.internal.definitions name = none)
    (externalFree : program.externals name = none)
    (addressFree : program.addresses logger = none) :
    let extended := withLogger program logger name effect internalFree externalFree addressFree
    extended.internal = program.internal ∧
    (Logging.Capability.present logger environment name effect).Bound extended ∧
    (∀ symbol fn, program.externals symbol = some fn → extended.externals symbol = some fn) ∧
    (CCallPolicy.ForeignAddresses program → CCallPolicy.ForeignAddresses extended) := by
  dsimp only
  refine ⟨rfl, ?_, ?_, ?_⟩
  · constructor
    · simp [withLogger, Linkage.withAddress]
    · exact Linkage.withExternal_bound program (External.observed (Logging.signature name) effect) internalFree externalFree
  · intro symbol fn found
    exact Linkage.withExternal_keeps program (External.observed (Logging.signature name) effect) internalFree externalFree found
  · intro foreign
    exact Linkage.withAddress_foreign
      (Linkage.withExternal program (External.observed (Logging.signature name) effect) internalFree externalFree)
      logger name addressFree
      ⟨_, Linkage.withExternal_bound program (External.observed (Logging.signature name) effect) internalFree externalFree⟩
      (Linkage.withExternal_foreign program (External.observed (Logging.signature name) effect) internalFree externalFree foreign)

/-- A symbolic importer name for a concrete nonvacuity witness. FMI passes a
function pointer, so this does not introduce a generated C symbol or require
that the native importer use this spelling. -/
def hostName : String := "__rumoca_importer_logger"

/-- The complete prepared environment, with an arbitrary logger effect and
any int32 rounding observation. All generated and library entries coexist. -/
def logged (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (boolean : interface.types "_Bool" = some .boolean)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32)
    (double : interface.types "double" = some .float64)
    (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
    (logger : Address) (effect : ReturningEffect (Logging.signature hostName)) : Events.Program Invocation :=
  withLogger (linked model sigs covered tag boolean size integer double observed range)
    logger hostName effect
    (unranked_undefined model sigs covered (by decide +kernel)) rfl rfl

theorem logged_contract (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (boolean : interface.types "_Bool" = some .boolean)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32)
    (double : interface.types "double" = some .float64)
    (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
    (logger : Address) (environment : Option Address)
    (effect : ReturningEffect (Logging.signature hostName)) :
    let program := logged model sigs covered tag boolean size integer double observed range logger effect
    program.internal = LiteralPreparation.program model sigs ∧
    (Logging.Capability.present logger environment hostName effect).Bound program ∧
    CCallPolicy.ForeignAddresses program ∧
    ProgramRanked functionRank program.internal ∧
    (∀ name fn, StaticRuntime.library tag boolean size integer name = some fn →
      program.externals name = some fn) ∧
    program.externals "floor" = some (CMathCalls.floorExternal double) ∧
    program.externals "fegetround" = some (CMathCalls.roundingExternal integer observed range) := by
  have base := linked_contract model sigs covered tag boolean size integer double observed range
  obtain ⟨_, foreign, ranked, statics, floor, rounding⟩ := base
  have extension := withLogger_contract
    (linked model sigs covered tag boolean size integer double observed range)
    logger environment hostName effect
    (unranked_undefined model sigs covered (by decide +kernel)) rfl rfl
  obtain ⟨_, callback, kept, preserves⟩ := extension
  exact ⟨rfl, callback, preserves foreign, ranked,
    fun name fn found => kept name fn (statics name fn found),
    kept _ _ floor, kept _ _ rounding⟩

/-- The constructed logger and library environment discharges the generic
scheduler theorem's pointer-boundary condition. No additional rank or address
policy is required from the caller of this theorem. -/
theorem logged_call_decreases (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (boolean : interface.types "_Bool" = some .boolean)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32)
    (double : interface.types "double" = some .float64)
    (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
    (logger : Address) (effect : ReturningEffect (Logging.signature hostName)) :
    let program := logged model sigs covered tag boolean size integer double observed range logger effect
    ∀ (fn : Function), program.internal.definitions caller = some (.tree fn) →
      LoopReady (fun e => e ∈ fn.body.flatMap statementCalls) state →
      Events.internalNext program (.body state resultType stack) = some (.calling name args after later) →
      program.internal.definitions name = some definition →
      (functionRank name).getD 0 < (functionRank caller).getD 0 := by
  intro program fn defined ready stepped target
  obtain ⟨_, _, foreign, ranked, _⟩ :=
    logged_contract model sigs covered tag boolean size integer double observed range logger none effect
  exact CCallPolicy.scheduled_internal_decreases program foreign ranked fn defined ready stepped target

end Rumoca.FMI3.RuntimeLinkage

namespace Rumoca.FMI3.RuntimeLinkage
open CTree CMemory CCalls CCalls.Events CCallPolicy CallPolicy

theorem rank_bounded (assigned : functionRank name = some r) : r ≤ 2 := by
  unfold functionRank at assigned
  split at assigned
  · simp only [Option.some.injEq] at assigned
    omega
  · split at assigned
    · simp only [Option.some.injEq] at assigned
      omega
    · split at assigned
      · simp only [Option.some.injEq] at assigned
        omega
      · contradiction

variable [interface : CInterface]

/-- Every reachable state in the constructed FMI environment has at most
three authored scheduler continuation frames. This excludes native library
and callback implementation frames and does not bound native stack bytes. -/
theorem logged_execution_depth (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (boolean : interface.types "_Bool" = some .boolean)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32)
    (double : interface.types "double" = some .float64)
    (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
    (logger : Address) (effect : ReturningEffect (Logging.signature hostName)) :
    let program := logged model sigs covered tag boolean size integer double observed range logger effect
    ∀ entry args before events target,
      Transition.Events.Reaches (Events.machine program).step
        (.calling entry args before .done) events target → CCallDepth.stateDepth target ≤ 3 := by
  intro program entry args before events target path
  obtain ⟨_, _, foreign, ranked, _⟩ :=
    logged_contract model sigs covered tag boolean size integer double observed range logger none effect
  exact CCallDepth.execution_depth_bound program foreign ranked
    (fun _ assigned => rank_bounded assigned) path

end Rumoca.FMI3.RuntimeLinkage
