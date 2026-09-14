import RumocaFMI3.ModelRhs

noncomputable section
namespace Rumoca.FMI3.ModelRhsRuntime
open CTree CMemory CCalls
variable [interface : CInterface]
set_option maxRecDepth 10000

/-- Only the helper's actual type and ordinary-symbol bindings are needed.
No successful helper or numerical execution is an assumption. -/
structure Types : Prop where
  model : interface.types "const Model *" = some .pointer
  result : interface.types "double" = some .float64
  rhs : interface.constants "rumoca_rhs" = none

theorem parameters_bound (types : Types) (p : Option Address) :
    parameters Runtime.helpers[1].signature.parameters [.pointer p] = some (ModelRhs.locals p) ∧
    CLoops.Calls.parameterTypes Runtime.helpers[1].signature.parameters = some ModelRhs.types := by
  have pointer : CBody.cast "const Model *" (.pointer p) = some (.pointer p) := by
    simp [CBody.cast, types.model, convert]
  constructor
  · simp [Runtime.helpers, parameters, parameterType, pointer, ModelRhs.locals]
  · simp [Runtime.helpers, CLoops.Calls.parameterTypes, parameterType, types.model, ModelRhs.types]

/-- The actual shared helper reaches the prepared Solve RHS through the
numerical C kernel, preserving the heap and the caller's continuation. -/
theorem reaches (program : Events.Program E) (types : Types)
    (model : Solve.Model source) (same : program.internal.kernel = CExecution.program model)
    (helper : program.internal.definitions "model_rhs" = some (.tree Runtime.helpers[1]))
    (numerical : program.internal.definitions "rumoca_rhs" = some (.kernel .rhs))
    (heap : Heap) (p : Option Address) (stack : Typed.Continuation) :
    Transition.Reaches (fun s t => Events.internalNext program s = some t)
      (.calling "model_rhs" [.pointer p] heap stack)
      (.returning (.finite model.realRhs) heap stack) := by
  obtain ⟨bound, typed⟩ := parameters_bound types p
  refine .next (Events.tree_entry program "model_rhs" [.pointer p] heap stack
    Runtime.helpers[1] (ModelRhs.locals p) ModelRhs.types helper bound typed) ?_
  refine .next (t := .calling "rumoca_rhs" [] heap (ModelRhs.continuation p stack)) ?_ ?_
  · simp [Events.internalNext, Typed.nextWith, CLoops.next, CLoops.eval,
      Runtime.helpers, Runtime.ret, Runtime.call, Runtime.v, CBody.eval,
      Events.enterCall, Events.resolve, Indirect.operand, Indirect.resolve,
      arguments, ModelRhs.locals, CBody.bind, CBody.resolve, CBody.constants,
      types.rhs, ModelRhs.continuation]
  refine .next (t := .kernel (.entry .rhs Binary64.positiveZero ⟨0, by decide +kernel⟩)
    heap (ModelRhs.continuation p stack)) ?_ ?_
  · simp [Events.internalNext, Typed.nextWith, numerical, kernelEntry]
  refine (Events.kernel_correct program model same .rhs Binary64.positiveZero
    ⟨0, by decide +kernel⟩ heap (ModelRhs.continuation p stack)).trans (.next ?_ (.refl _))
  simp [Events.internalNext, Typed.nextWith, Typed.resume, ModelRhs.continuation,
    returnCast, CBody.cast, types.result, convert, CStatements.result, Value.finite]

theorem behaviors (program : Events.Program E) (types : Types)
    (model : Solve.Model source) (same : program.internal.kernel = CExecution.program model)
    (helper : program.internal.definitions "model_rhs" = some (.tree Runtime.helpers[1]))
    (numerical : program.internal.definitions "rumoca_rhs" = some (.kernel .rhs))
    (heap : Heap) (p : Option Address) (behavior) :
    (Events.machine program).Behaves (.calling "model_rhs" [.pointer p] heap .done) behavior ↔
      behavior = .terminates [] ⟨.finite model.realRhs, heap⟩ :=
  (Events.internal_prefix program (reaches program types model same helper numerical heap p .done)
    (Events.return_forced program _ heap)).behaviors behavior

end Rumoca.FMI3.ModelRhsRuntime
end
