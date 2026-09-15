import RumocaC.StorageLibrary
import RumocaFMI3.RuntimeLinkage

/-! The complete prepared runtime preserves modeled storage under an explicit callback contract; arbitrary changes are attributed to an actual logger call. -/
noncomputable section
namespace Rumoca.FMI3.RuntimeStorage
open CTree CMemory CCalls CCalls.Events CStoreInvariant CStorage RuntimeLinkage
variable [interface : CInterface]

theorem static_library (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32)
    (found : StaticRuntime.library tag boolean size integer name = some fn) :
    ExternalPreserves Preserves fn := by
  unfold StaticRuntime.library at found
  split at found
  · cases Option.some.inj found; exact exchange_external tag boolean
  · cases Option.some.inj found; exact write_external tag
  · exact string_library size integer found

theorem linked_storage (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32)
    (double : interface.types "double" = some .float64)
    (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31) :
    ProgramPreserves Preserves (linked model sigs covered tag boolean size integer double observed range) := by
  exact linked_external _ _
    (unranked_undefined model sigs covered (by change CallPolicy.functionRank "fegetround" = none; decide +kernel)) rfl
    (linked_external _ _
      (unranked_undefined model sigs covered (by change CallPolicy.functionRank "floor" = none; decide +kernel)) rfl
      (fun _ _ found => static_library tag boolean size integer found) (floor_external double))
    (rounding_external integer observed range)

/-- The generated/library environment preserves object storage. The added
callback needs a separately stated storage contract for the same conclusion. -/
theorem logger_storage (program : Events.Program Invocation) (logger : Address)
    (name : String) (effect : ReturningEffect (Logging.signature name))
    (internalFree : program.internal.definitions name = none)
    (externalFree : program.externals name = none)
    (addressFree : program.addresses logger = none)
    (previous : ProgramPreserves Preserves program)
    (callback : ∀ args before result after, effect.execute args before result after → Preserves before after) :
    ProgramPreserves Preserves
      (withLogger program logger name effect internalFree externalFree addressFree) := by
  change ProgramPreserves Preserves
    (Linkage.withExternal program (External.observed (Logging.signature name) effect) internalFree externalFree)
  apply linked_external _ _ internalFree externalFree previous
  intro args before events result after executed
  exact callback args before result after executed.2

theorem logged_storage (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (boolean : interface.types "_Bool" = some .boolean)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32)
    (double : interface.types "double" = some .float64)
    (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
    (logger : Address) (effect : ReturningEffect (Logging.signature hostName))
    (callback : ∀ args before result after, effect.execute args before result after → Preserves before after) :
    ProgramPreserves Preserves (logged model sigs covered tag boolean size integer double observed range logger effect) :=
  logger_storage _ _ _ _ _ _ _
    (linked_storage model sigs covered tag boolean size integer double observed range) callback

/-- All finite prefixes, including partial/stuck/divergent runs, preserve
modeled object existence, types and permissions under the explicit callback
storage policy. Native/transient library allocation is not modeled by this claim. -/
theorem logged_resources (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (boolean : interface.types "_Bool" = some .boolean)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32)
    (double : interface.types "double" = some .float64)
    (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
    (logger : Address) (effect : ReturningEffect (Logging.signature hostName))
    (callback : ∀ args before result after, effect.execute args before result after → Preserves before after) :
    let program := logged model sigs covered tag boolean size integer double observed range logger effect
    ∀ entry args before events target,
      Transition.Events.Reaches (Events.machine program).step
        (.calling entry args before .done) events target →
      Preserves before (CReadOnly.typedHeap target) ∧ CCallDepth.stateDepth target ≤ 3 := by
  intro program entry args before events target path
  exact ⟨event_reaches stable Preserves.trans
    (logged_storage model sigs covered tag boolean size integer double observed range logger effect callback) path,
    logged_execution_depth model sigs covered tag boolean size integer double observed range logger effect _ _ _ _ _ path⟩
end Rumoca.FMI3.RuntimeStorage

namespace Rumoca.FMI3.RuntimeStorage
open CTree CMemory CCalls CCalls.Events CStoreInvariant CStorage RuntimeLinkage
variable [CInterface]

/-- Only the explicitly added importer can change object storage when the
previous runtime bindings preserve it. This classifies an executed call, not
merely a symbol occurring somewhere in the generated text. -/
theorem logger_change (program : Events.Program Invocation) (logger : Address)
    (name : String) (effect : ReturningEffect (Logging.signature name))
    (internalFree : program.internal.definitions name = none)
    (externalFree : program.externals name = none)
    (addressFree : program.addresses logger = none)
    (previous : ProgramPreserves Preserves program)
    (found : (withLogger program logger name effect internalFree externalFree addressFree).externals target = some fn)
    (executed : fn.execute args before events result after)
    (changed : ¬ Preserves before after) :
    target = name ∧ fn = External.observed (Logging.signature name) effect ∧
      events = [⟨name, args⟩] ∧ effect.execute args before result after := by
  change (if target = name then some (External.observed (Logging.signature name) effect)
    else program.externals target) = some fn at found
  by_cases same : target = name
  · simp only [if_pos same, Option.some.injEq] at found
    subst fn
    exact ⟨same, rfl, executed⟩
  · have old : program.externals target = some fn := by
      simpa only [if_neg same] using found
    exact False.elim (changed (previous target fn old args before events result after executed))

/-- Storage changes in the complete prepared runtime can be attributed to an
actual logger call in that execution. No restriction on the logger is added. -/
theorem logged_change_origin (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (boolean : CInterface.types "_Bool" = some .boolean)
    (size : CInterface.types "size_t" = some .size)
    (integer : CInterface.types "int" = some .int32)
    (double : CInterface.types "double" = some .float64)
    (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
    (logger : Address) (effect : ReturningEffect (Logging.signature hostName)) :
    let program := logged model sigs covered tag boolean size integer double observed range logger effect
    ∀ s events t,
      Transition.Events.Reaches (Events.machine program).step s events t →
      ¬ Preserves (CReadOnly.typedHeap s) (CReadOnly.typedHeap t) →
      ∃ preEvents suffix args values before result after stack,
        Transition.Events.Reaches (Events.machine program).step s preEvents
          (.calling hostName args before stack) ∧
        convertedArguments (Logging.signature hostName).parameters args = some values ∧
        effect.execute values before result after ∧ ¬ Preserves before after ∧
        Transition.Events.Reaches (Events.machine program).step
          (.returning result after stack) suffix t ∧
        events = preEvents ++ [⟨hostName, values⟩] ++ suffix := by
  intro program s events t path changed
  obtain ⟨preEvents, callEvents, suffix, name, fn, args, values, before, result, after, stack,
    entered, bound, converted, executed, altered, returns, trace⟩ :=
    foreign_change_origin stable Preserves.trans path changed
  obtain ⟨same, fnSame, callTrace, effectRan⟩ :=
    logger_change _ logger hostName effect
      (unranked_undefined model sigs covered (by decide +kernel)) rfl rfl
      (linked_storage model sigs covered tag boolean size integer double observed range)
      bound executed altered
  cases same
  cases fnSame
  exact ⟨preEvents, suffix, args, values, before, result, after, stack,
    entered, converted, effectRan, altered, returns, by rw [trace, callTrace]⟩
end Rumoca.FMI3.RuntimeStorage
