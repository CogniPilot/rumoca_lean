import RumocaC.Fenv
import RumocaC.BodyCallInterface
import RumocaFMI3.TimeCalls
import RumocaFMI3.ModelAdvance

/-! The static runtime, literal pool and explicit fenv header share one
interface. These call consequences do not certify the native header, flags,
full public CS call or arbitrary surrounding host histories. -/
noncomputable section
namespace Rumoca.FMI3.RuntimeEnvironment
open CTree CMemory StaticFactory CLiteral.Interface

abbrev interface (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses) : CInterface :=
  header.interface (executionInterface objects literals)

theorem types_agree (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses) :
    (cInterface literals).types = (interface header objects literals).types :=
  StaticInitialization.interface_types objects literals

theorem time_body_agrees (header : CFenv.Header) (model : Solve.FMI3Model source)
    (objects : Objects) (literals : CLiteralAddresses) :
    CodeAgrees (cInterface literals) (interface header objects literals)
      (Runtime.body model TimeCalls.signature) := by
  rw [TimeCalls.body]
  simp [CodeAgrees, StmtAgrees, ExprAgrees, names, TimeCalls.tail, Runtime.require,
    Runtime.instancePrefix, Runtime.modeGuard, Runtime.allowedExpression, permittedModes,
    Runtime.put, Runtime.invalidTime, Runtime.mode, Runtime.ok, Runtime.reject, Runtime.fail,
    Runtime.branch, Runtime.ret, Runtime.any, Runtime.both, Runtime.either, Runtime.negate,
    Runtime.eqv, Runtime.field, Runtime.finite, Runtime.lt, Runtime.gt, Runtime.call,
    Runtime.v, Runtime.n, Expr.nullPointer, interface, CFenv.Header.interface, CInterface.constants,
    objectConstants]

/-- The actual admitted ME time call executes in the interface that also
supplies the CS rounding macro. Other functions may use that binding. -/
theorem time_call_behaviors {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := interface header objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p : Address)
      (window : Time.Window) (minimum time : Binary64.Value) (old : Option Value),
      program.internal.definitions TimeCalls.signature.name =
        some (.tree (Runtime.function model TimeCalls.signature)) →
      load heap (p.member "kind") = some (.integer 0) →
      load heap (p.member "mode") = some (.integer 3) →
      TimeCalls.Bounds heap p window minimum →
      heap (p.member "time") = some ⟨.float64, true, old⟩ → window.Admissible time →
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling TimeCalls.signature.name
          (TimeCalls.arguments (some p) (Binary64.toBits time).val) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0,
          StateProofs.written heap (p.member "time") (Binary64.toBits time).val⟩ := by
  letI : CInterface := interface header objects literals
  intro program heap p window minimum time old defined kind mode bounds writable admissible behavior
  have executed := TimeProofs.set_run (static := ⟨literals⟩) model TimeCalls.signature rfl
    heap p window minimum time old kind mode bounds.lower bounds.minimumValue
    bounds.stopDefined bounds.stopValue writable admissible
  have parameters := TimeCalls.parameters_bound literals (some p) (Binary64.toBits time).val
  rw [TimeCalls.finite_parameters] at parameters
  exact CCalls.Events.body_call_interface_behaviors (cInterface literals)
    (interface header objects literals) (types_agree header objects literals) rfl
    program (Runtime.function model TimeCalls.signature) _ _ heap _ (.integer 0) 6
    defined parameters (BodyEmbedding.body_closed model TimeCalls.signature)
    (time_body_agrees header model objects literals) executed rfl behavior

/-- Reuse the existing quiet-call contract in the extended environment,
including null handles without assuming any instance storage. -/
theorem time_quiet {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := interface header objects literals
    ∀ (program : CCalls.Events.Program E),
      program.internal.definitions TimeCalls.signature.name =
        some (.tree (Runtime.function model TimeCalls.signature)) →
      TimeCalls.QuietContract program := by
  letI : CInterface := interface header objects literals
  intro program defined
  constructor
  · intro heap p window minimum time old
    exact time_call_behaviors header objects literals model program heap p window minimum time old defined
  · intro heap bits behavior
    let rest := Runtime.modeGuard .setTime ::
      Runtime.reject Runtime.invalidTime TimeCalls.message :: TimeCalls.tail
    have executed := GuardedCalls.null_body (static := ⟨literals⟩)
      (TimeCalls.parameters none bits) heap rest
      (by simp [TimeCalls.parameters, CBody.bind])
      (by simp [TimeCalls.parameters, CBody.bind])
      (by simp [TimeCalls.parameters, CBody.bind])
    have body : (Runtime.function model TimeCalls.signature).body = Runtime.instancePrefix ++ rest := by
      simp [Runtime.function, TimeCalls.body, Runtime.require, rest, List.append_assoc]
    rw [← body] at executed
    exact CCalls.Events.body_call_interface_behaviors (cInterface literals)
      (interface header objects literals) (types_agree header objects literals) rfl
      program (Runtime.function model TimeCalls.signature) _ _ heap _ (.integer 3) 3
      defined (TimeCalls.parameters_bound literals none bits)
      (BodyEmbedding.body_closed model TimeCalls.signature)
      (time_body_agrees header model objects literals) executed rfl behavior

/-- The actual solver helper uses the same header/object/literal context.
Its numerical machine remains the declared nearest-even profile; native fenv
correspondence is a separate obligation. -/
theorem model_advance_behaviors (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) (signatures : List Signature)
    (fresh : LiteralPreparation.KernelNamesFresh signatures) :
    letI : CInterface := interface header objects literals
    ∀ (program : CCalls.Events.Program E),
      program.internal = LiteralPreparation.program model signatures →
      ∀ (heap : Heap) (p : Address) (x : Binary64.Value) (count : CStatements.Counter),
      heap (p.member "x") = some ⟨.float64, true, some (.finite x)⟩ →
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "model_advance" [.pointer (some p), .integer count.val] heap .done) behavior ↔
        behavior = .terminates [] ⟨.void,
          StateProofs.written heap (p.member "x") (Binary64.toBits (model.solve.run x count.val)).val⟩ := by
  letI : CInterface := interface header objects literals
  intro program actual heap p x count stored behavior
  have types : ModelAdvance.Types := ⟨rfl, rfl, rfl⟩
  apply ModelAdvance.advance_behaviors program types model.solve (by rw [actual]; rfl)
    _ _ heap p x count stored behavior
  · rw [actual]
    exact LiteralPreparation.helpers_bound model signatures Runtime.helpers[2] (by simp [Runtime.helpers])
  · rw [actual]
    exact LiteralPreparation.numerical_bound model signatures fresh .sample

end Rumoca.FMI3.RuntimeEnvironment
end
