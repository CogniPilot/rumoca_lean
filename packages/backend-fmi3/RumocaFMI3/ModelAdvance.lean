import RumocaFMI3.NumericalBindings
import RumocaFMI3.StaticFactoryEnvironment
import RumocaFMI3.StateProofs
import RumocaC.KernelEvents

/-! Actual numerical helper bodies in the same typed/eventful scheduler used
by public calls. No successful helper execution is supplied as a premise. -/
noncomputable section
namespace Rumoca.FMI3.ModelAdvance
set_option maxRecDepth 10000
open CTree CMemory CCalls
variable [interface : CInterface]

structure Types : Prop where
  model : interface.types "Model *" = some .pointer
  count : interface.types "uint64_t" = some .size
  sample : interface.constants "rumoca_sample" = none

def advanceLocals (p : Address) (n : CStatements.Counter) : CBody.Locals :=
  CBody.bind (CBody.bind (fun _ => none) "count" (.integer n.val)) "model" (.pointer (some p))
def advanceTypes : CLoops.Types :=
  CLoops.bindType (CLoops.bindType (fun _ => none) "count" .size) "model" .pointer

theorem advance_parameters (types : Types) (p : Address) (n : CStatements.Counter) :
    parameters Runtime.helpers[2].signature.parameters [.pointer (some p), .integer n.val] =
      some (advanceLocals p n) ∧
      CLoops.Calls.parameterTypes Runtime.helpers[2].signature.parameters = some advanceTypes := by
  have pointer : CBody.cast "Model *" (.pointer (some p)) = some (.pointer (some p)) := by
    simp [CBody.cast, types.model, convert]
  have count : CBody.cast "uint64_t" (.integer n.val) = some (.integer n.val) :=
    CLoops.Calls.cast_of_type "uint64_t" .size _ _ types.count (CLoops.convert_size_nat n.val n.isLt)
  constructor
  · simp [Runtime.helpers, parameters, parameterType, pointer, count, advanceLocals, CBody.bind]
  · simp [Runtime.helpers, CLoops.Calls.parameterTypes, parameterType, types.model, types.count,
      CLoops.bindType, advanceTypes]

theorem advance_reaches (program : Events.Program E) (types : Types)
    (model : Solve.Model source) (same : program.internal.kernel = CExecution.program model)
    (helper : program.internal.definitions "model_advance" = some (.tree Runtime.helpers[2]))
    (kernel : program.internal.definitions "rumoca_sample" = some (.kernel .sample))
    (heap : Heap) (p : Address) (x : Binary64.Value) (n : CStatements.Counter)
    (stored : heap (p.member "x") = some ⟨.float64, true, some (.finite x)⟩)
    (stack : Typed.Continuation) :
    Transition.Reaches (fun s t => Events.internalNext program s = some t)
      (.calling "model_advance" [.pointer (some p), .integer n.val] heap stack)
      (.returning .void
        (StateProofs.written heap (p.member "x") (Binary64.toBits (model.run x n.val)).val) stack) := by
  let env := advanceLocals p n
  let saved := Typed.Continuation.caller (.assign (.field (.id "model") "x" true))
    [] env advanceTypes "void" stack
  let output := StateProofs.written heap (p.member "x") (Binary64.toBits (model.run x n.val)).val
  have loaded : load heap (p.member "x") = some (.finite x) := by
    simp [load, stored, Value.finite, convert]
  obtain ⟨bound, typed⟩ := advance_parameters types p n
  refine .next (Events.tree_entry program _ _ _ stack _ _ _ helper bound typed) ?_
  refine .next (t := .calling "rumoca_sample" [.finite x, .integer n.val] heap saved) ?_ ?_
  · simp [Events.internalNext, Typed.nextWith, CLoops.next, CLoops.eval,
      Events.enterCall, Events.resolve, Indirect.resolve, Indirect.operand,
      CBody.eval, CBody.resolve, CBody.constants, arguments, Runtime.helpers,
      Runtime.call, Runtime.v, env, advanceLocals, CBody.bind, types.sample, saved,
      Value.address, loaded]
  refine .next (t := .kernel (.entry .sample x n) heap saved) ?_ ?_
  · simp [Events.internalNext, Typed.nextWith, kernel, kernelEntry]
  refine (Events.kernel_correct program model same .sample x n heap saved).trans
    (.next (t := .body (.running [] env advanceTypes output) "void" stack) ?_
      (.next ?_ (.refl _)))
  · simp [Events.internalNext, Typed.nextWith, Typed.resume, saved, CBody.lvalue,
      CBody.eval, CBody.resolve, CBody.constants, env, advanceLocals, CBody.bind,
      Value.address, CStatements.result, Value.finite, store_float64 heap (p.member "x") _ _ stored,
      output, StateProofs.written]
  · rfl

theorem advance_behaviors (program : Events.Program E) (types : Types)
    (model : Solve.Model source) (same : program.internal.kernel = CExecution.program model)
    (helper : program.internal.definitions "model_advance" = some (.tree Runtime.helpers[2]))
    (kernel : program.internal.definitions "rumoca_sample" = some (.kernel .sample))
    (heap : Heap) (p : Address) (x : Binary64.Value) (n : CStatements.Counter)
    (stored : heap (p.member "x") = some ⟨.float64, true, some (.finite x)⟩) (behavior) :
    (Events.machine program).Behaves
      (.calling "model_advance" [.pointer (some p), .integer n.val] heap .done) behavior ↔
      behavior = .terminates [] ⟨.void,
        StateProofs.written heap (p.member "x") (Binary64.toBits (model.run x n.val)).val⟩ := by
  exact Transition.Events.Forced.behaviors
    (Events.internal_prefix program
      (advance_reaches program types model same helper kernel heap p x n stored .done)
      (Events.return_forced program _ _)) behavior

omit interface in
theorem static_types (objects : StaticFactory.Objects) (literals : CLiteralAddresses) :
    @Types (StaticFactory.executionInterface objects literals) := by
  letI : CInterface := StaticFactory.executionInterface objects literals
  exact ⟨rfl, rfl, rfl⟩

omit interface in
theorem prepared_behaviors (model : Solve.FMI3Model source) (signatures : List Signature)
    (fresh : LiteralPreparation.KernelNamesFresh signatures)
    (objects : StaticFactory.Objects) (literals : CLiteralAddresses) :
    letI : CInterface := StaticFactory.executionInterface objects literals
    ∀ (program : Events.Program E),
    program.internal = LiteralPreparation.program model signatures →
    ∀ (heap : Heap) (p : Address) (x : Binary64.Value) (n : CStatements.Counter),
    heap (p.member "x") = some ⟨.float64, true, some (.finite x)⟩ →
    ∀ behavior, (Events.machine program).Behaves
      (.calling "model_advance" [.pointer (some p), .integer n.val] heap .done) behavior ↔
      behavior = .terminates [] ⟨.void,
        StateProofs.written heap (p.member "x") (Binary64.toBits (model.solve.run x n.val)).val⟩ := by
  letI : CInterface := StaticFactory.executionInterface objects literals
  intro program actual heap p x n stored behavior
  apply advance_behaviors program (static_types objects literals) model.solve
    (by rw [actual]; rfl) _ _ heap p x n stored behavior
  · rw [actual]
    exact LiteralPreparation.helpers_bound model signatures Runtime.helpers[2]
      (by simp [Runtime.helpers])
  · rw [actual]
    exact LiteralPreparation.numerical_bound model signatures fresh .sample

omit interface in
theorem written_frame (heap : Heap) (p query : Address) (x : Binary64.Value)
    (other : query ≠ p.member "x") :
    StateProofs.written heap (p.member "x") (Binary64.toBits x).val query = heap query :=
  StateProofs.written_frame heap _ query _ other

end Rumoca.FMI3.ModelAdvance
end
