import RumocaFMI3.DebugLoggingCalls
import RumocaFMI3.RuntimeEnvironment
import RumocaFMI3.LiteralPreparation
import RumocaC.StringLiteralContents

/-! Bind public logging to the same static objects, fenv header, definition
table and immutable literals used by creation and later lifecycle calls.
The emitter-equality premise must be discharged by the actual artifact contract. -/
noncomputable section
namespace Rumoca.FMI3.DebugLogging
open CTree CMemory StaticFactory CLiteral CStringMemory

def failureMessage (unknown : Bool) : String :=
  if unknown then "Unknown log category" else "Missing log categories"

theorem message_collected (unknown : Bool) :
    failureMessage unknown ∈ functionTexts function := by
  cases unknown <;>
    simp [failureMessage, function, code, missing, failure, validation, CLoops.loop,
      iteration, rejectNull, comparison, rejectDifference, finish, writeLogging,
      Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.reject,
      Runtime.branch, Runtime.fail, Runtime.ret, Runtime.call, Runtime.v,
      functionTexts, statementTexts, expressionTexts]

theorem runtime_types (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses) :
    @DebugLogging.EntryTypes (RuntimeEnvironment.interface header objects literals) := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem runtime_library (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E),
      program.externals "strcmp" = some (CStringCalls.compareExternal (by rfl)) →
      Library program := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program binding
  exact ⟨rfl, rfl, rfl, rfl, binding, rfl, rfl⟩

theorem prepared_definitions (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature ∈ sigs) (emitted : Runtime.function model signature = function)
    (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E), program.internal = LiteralPreparation.program model sigs →
      program.internal.definitions signature.name = some (.tree function) ∧
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program actual
  constructor
  · rw [actual, ← emitted]
    exact LiteralPreparation.function_bound model sigs unique signature member
  · rw [actual]
    exact LiteralPreparation.helpers_bound model sigs Runtime.helpers[0] (by simp [Runtime.helpers])

/-- All literal addresses and readable contents are constructed from the
actual function collection. Later heaps need only preserve its immutable pool. -/
theorem prepared_literals (model : Solve.FMI3Model source) (sigs : List Signature)
    (member : signature ∈ sigs) (emitted : Runtime.function model signature = function)
    {pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare model sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap) :
    ∃ (category : Address) (messages : Bool → Address),
      pool.addresses firstBlock "logStatus" = some category ∧
      (∀ unknown, pool.addresses firstBlock (failureMessage unknown) = some (messages unknown)) ∧
      Contents heap category (content "logStatus") ∧
      (∀ unknown, Stored signed heap (messages unknown) (failureMessage unknown)) := by
  have categoryCollected : "logStatus" ∈ functionTexts Runtime.helpers[0] := by
    simp [Runtime.helpers, Runtime.setMode, Runtime.put, Runtime.mode, Runtime.log,
      Runtime.branch, Runtime.both, Runtime.field, Runtime.ret, Runtime.v, Runtime.n,
      functionTexts, statementTexts, expressionTexts]
  obtain ⟨category, categoryBound⟩ := LiteralPreparation.text_bound model sigs made Runtime.helpers[0]
    (List.mem_append_left _ (by simp [Runtime.helpers])) "logStatus" categoryCollected firstBlock
  have each : ∀ unknown, ∃ message,
      pool.addresses firstBlock (failureMessage unknown) = some message := by
    intro unknown
    apply LiteralPreparation.message_bound model sigs made signature member (failureMessage unknown)
    · rw [emitted]
      exact message_collected unknown
  choose messages bound using each
  exact ⟨category, messages, categoryBound, bound,
    literal_contents ((pool.storage_valid before firstBlock signed _ _ categoryBound).preserved frame),
    fun unknown => (pool.storage_valid before firstBlock signed _ _ (bound unknown)).preserved frame⟩

end Rumoca.FMI3.DebugLogging
end
