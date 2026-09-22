import RumocaC.KernelEvents
import RumocaFMI3.NumericalBindings
import RumocaFMI3.BodyEmbedding
import RumocaFMI3.RuntimePrinter

noncomputable section
namespace Rumoca.FMI3.ModelRhs
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses
open CTree CMemory

def locals (p : Option Address) : CBody.Locals :=
  CBody.bind (fun _ => none) "model" (.pointer p)

def types : CLoops.Types := CLoops.bindType (fun _ => none) "model" .pointer

def continuation (p : Option Address) (stack : CCalls.Typed.Continuation) : CCalls.Typed.Continuation :=
  .caller .ret [] (locals p) types "double" stack

theorem parameters_bound (p : Option Address) :
    CCalls.parameters Runtime.helpers[1].signature.parameters [.pointer p] = some (locals p) := by
  rfl

theorem types_bound : CLoops.Calls.parameterTypes Runtime.helpers[1].signature.parameters = some types := by
  rfl

set_option maxRecDepth 10000 in
theorem call_numerical (program : CCalls.Events.Program E) (heap : Heap)
    (p : Option Address) (stack : CCalls.Typed.Continuation) :
    CCalls.Events.internalNext program
      (.body (.running Runtime.helpers[1].body (locals p) types heap) "double" stack) =
      some (.calling "rumoca_rhs" [] heap (continuation p stack)) := by
  simp [CCalls.Events.internalNext, CCalls.Events.internalNextWith, CCalls.Typed.nextWithExpressions, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions,
    Runtime.helpers, Runtime.ret, Runtime.call, Runtime.v, CBody.eval, CBody.evalWith,
    CCalls.Events.enterCallWith, CCalls.Events.resolveWith, CCalls.Indirect.operand,
    CCalls.Indirect.resolveWith, CBody.legacyExpressions, CCalls.argumentsWith, CBody.legacyExpressions, locals, CBody.bind, CBody.resolve,
    CBody.constants, continuation]

/-- Actual helper entry, nested numerical C execution and converted return.
Its unused model argument may be null; no heap cell is read or changed. -/
theorem reaches (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (p : Option Address) (stack : CCalls.Typed.Continuation)
    (helper : program.internal.definitions "model_rhs" = some (.tree Runtime.helpers[1]))
    (numerical : program.internal.definitions "rumoca_rhs" = some (.kernel .rhs))
    (same : program.internal.kernel = CExecution.program model.solve) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.calling "model_rhs" [.pointer p] heap stack)
      (.returning (.finite model.solve.realRhs) heap stack) := by
  refine .next (CCalls.Events.tree_entry program "model_rhs" [.pointer p] heap stack
    Runtime.helpers[1] (locals p) types helper (parameters_bound p) types_bound) ?_
  refine .next (call_numerical program heap p stack) ?_
  refine .next (t := .kernel (.entry .rhs Binary64.positiveZero ⟨0, by decide +kernel⟩)
    heap (continuation p stack)) ?_ ?_
  · simp [CCalls.Events.internalNext, CCalls.Events.internalNextWith, CCalls.Typed.nextWithExpressions, numerical, CCalls.kernelEntry]
  refine (CCalls.Events.kernel_correct program model.solve same .rhs Binary64.positiveZero
    ⟨0, by decide +kernel⟩ heap (continuation p stack)).trans (.next ?_ (.refl _))
  simp [CCalls.Events.internalNext, CCalls.Events.internalNextWith, CCalls.Typed.nextWithExpressions, CCalls.Typed.resumeWith,
    continuation, CCalls.returnCast, CBody.cast, convert, CStatements.result, Value.finite]

theorem behaviors (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (p : Option Address)
    (helper : program.internal.definitions "model_rhs" = some (.tree Runtime.helpers[1]))
    (numerical : program.internal.definitions "rumoca_rhs" = some (.kernel .rhs))
    (same : program.internal.kernel = CExecution.program model.solve) (behavior) :
    (CCalls.Events.machine program).Behaves (.calling "model_rhs" [.pointer p] heap .done) behavior ↔
      behavior = .terminates [] ⟨.finite model.solve.realRhs, heap⟩ :=
  (CCalls.Events.internal_prefix program (reaches model program heap p .done helper numerical same)
    (CCalls.Events.return_forced program _ heap)).behaviors behavior

end Rumoca.FMI3.ModelRhs

noncomputable section
namespace Rumoca.FMI3.ModelRhs
open CTree CMemory

structure FunctionContract (model : Solve.FMI3Model source) (sigs : List Signature) (text : String) : Prop where
  fresh : LiteralPreparation.KernelNamesFresh sigs
  printed : text = Runtime.helpers[1].render
  tokenization : Printer.FunctionTokenization RuntimePrinter.typedefs text Runtime.helpers[1]
  execution : ∀ (static : StaticLiterals) (E : Type)
    (program : @CCalls.Events.Program (cInterface static.addresses) E),
    @CCalls.Events.Program.internal (cInterface static.addresses) E program = LiteralPreparation.program model sigs →
    ∀ heap p behavior, (@CCalls.Events.machine E (cInterface static.addresses) program).Behaves
      (.calling "model_rhs" [.pointer p] heap .done) behavior ↔
      behavior = .terminates [] ⟨.finite model.solve.realRhs, heap⟩

theorem rendered_contract (model : Solve.FMI3Model source) (sigs : List Signature)
    (fresh : LiteralPreparation.KernelNamesFresh sigs) :
    FunctionContract model sigs Runtime.helpers[1].render := by
  refine ⟨fresh, rfl, ?_, ?_⟩
  · exact (Printer.function_denotes (RuntimePrinter.helpers_printable Runtime.helpers[1]
      (by simp [Runtime.helpers]))).tokenization
  · intro static E program same heap p behavior
    apply behaviors model program heap p
    · rw [same]
      exact LiteralPreparation.helpers_bound model sigs Runtime.helpers[1] (by simp [Runtime.helpers])
    · rw [same]
      exact LiteralPreparation.numerical_bound model sigs fresh .rhs
    · rw [same]
      exact LiteralPreparation.numerical_program model sigs

end Rumoca.FMI3.ModelRhs
