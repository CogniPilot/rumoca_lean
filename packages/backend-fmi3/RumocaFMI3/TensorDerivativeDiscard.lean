import RumocaFMI3.TensorDerivativeAdmission
import RumocaC.TensorSquareDiagonal
import RumocaCore.Array.ADFiniteSquare

/-! Numerical failure of the checked derivative entry. The full original heap
is preserved before any callback; every represented callback outcome and the
no-outcome case are retained. The emitted adapter's mandatory actual-artifact
contract includes these obligations alongside its original success guarantees. -/
noncomputable section
namespace Rumoca.FMI3.TensorDerivativeDiscard
open CTree CMemory CBody CLoops TensorInstance TensorContinuousStates CTensor
open CMemory.TensorView
set_option maxRecDepth 10000

variable [static : StaticLiterals]
private local instance : CInterface := cInterface static.addresses

omit static in
/-- Every finite input either admits the old Solve execution and all Jacobian
additions, or has an independent real square-overflow witness. -/
theorem outcomes_total (state input : Values shape) :
    (Solve.Tensor.Numerical.allFiniteBits (MultiplicationTotal.result input input) = true ∧
      (∃ result, Solve.Tensor.Finite.Executes (ArrayProfile.squareProgram shape)
        (ArrayProfile.environment state input) result) ∧
      ∀ k : Fin shape.volume, Binary64.Adds input[k] input[k]
        (.finite (SquareDiagonal.doubled input)[k])) ∨
    (Solve.Tensor.Numerical.allFiniteBits (MultiplicationTotal.result input input) = false ∧
      ∃ k : Fin shape.volume,
        Binary64.overflowValue ≤ Binary64.value input[k] * Binary64.value input[k]) := by
  cases classified : Solve.Tensor.Numerical.allFiniteBits (MultiplicationTotal.result input input) with
  | false => exact Or.inr ⟨rfl, (ProductPreflight.square_overflow input).1 classified⟩
  | true =>
    refine Or.inl ⟨rfl, (ProductPreflight.square_finite_execution state input).1 classified, ?_⟩
    intro k
    rw [SquareDiagonal.doubled_get]
    exact Binary64.ADExact.adds_self_of_finite_square _
      ((MultiplicationTotal.result_allFinite input input).1 classified k)

def context : ErrorContext static.addresses where
  target := cInterface static.addresses
  types := rfl
  bytes := rfl
  helper := by
    simp [CLiteral.Interface.CodeAgrees, CLiteral.Interface.StmtAgrees, CLiteral.Interface.ExprAgrees,
      CLiteral.Interface.names, Runtime.helpers, Runtime.setMode, Runtime.put, Runtime.mode,
      Runtime.log, Runtime.branch, Runtime.ret, Runtime.v, Runtime.n, Runtime.field, Runtime.both]
  error := rfl
  ordinary := rfl

def Path (program : CCalls.Events.Program E) (start : CCalls.Typed.State)
    (heap : Heap) (p : Address) : Prop :=
  ∃ env types rest, Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      start (.body (.running (Discard.body TensorDerivativePreflight.message ++ rest) env types heap)
        "fmi3Status" .done) ∧
    resolve env "m" = some (.pointer (some p)) ∧ resolve env "fmi3Discard" = some (.integer 2)

theorem public_prefix (program : CCalls.Events.Program E) (shape : Tensor.Shape) (hasOutput : Bool)
    (heap : Heap) (p buffer : Address) (count : UInt64) (kind : Kind) (mode : Mode)
    (input : Values shape) (matched : count.toNat = shape.volume) (bounded : shape.volume < 2 ^ 64)
    (defined : program.internal.definitions "fmi3GetContinuousStateDerivatives" =
      some (.tree (derivCheckedFunction shape hasOutput)))
    (kindValue : load heap (p.member "kind") = some (.integer kind.code))
    (modeValue : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getDerivatives kind mode)
    (readable : Reads heap (p.member inputName) input)
    (overflow : ∃ k : Fin shape.volume,
      Binary64.overflowValue ≤ Binary64.value input[k] * Binary64.value input[k]) :
    Path program (.calling "fmi3GetContinuousStateDerivatives"
      (DerivativeCalls.values (some p) (some buffer) count) heap .done) heap p := by
  obtain ⟨prior, entered⟩ := TensorDerivativeAdmission.entry program shape hasOutput heap p buffer count
    kind mode .done matched defined kindValue modeValue allowed
  let rest := .eval (Runtime.call "rumoca_rhs" derivEntryArgs) :: derivCheckedTail shape hasOutput
  have failed := TensorDerivativePreflight.failure (derivGuardEnv p buffer count) prior heap p input rest
    (by simp [derivGuardEnv, CBody.bind])
    (by simp [derivGuardEnv, derivParameters, CBody.bind, matched])
    (by intro name member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp [derivGuardEnv, derivParameters, CBody.bind]) readable bounded
    ((ProductPreflight.square_overflow input).2 overflow)
  refine ⟨TensorDerivativePreflight.finalEnv (derivGuardEnv p buffer count) p input,
    TensorDerivativePreflight.finalTypes prior, rest,
    entered.trans (CCalls.Events.body_reaches program failed "fmi3Status" .done), ?_, ?_⟩
  · simp [CBody.resolve, (TensorDerivativeContinuation.after_preflight p buffer count input).instanceValue]
  · have unchanged := ProductPreflight.Inline.final_frame (derivGuardEnv p buffer count)
      (some (p.member inputName)) (some (p.member inputName)) input input "fmi3Discard" (by simp)
    simp only [CBody.resolve, TensorDerivativePreflight.finalEnv, unchanged]
    rfl

theorem suppressed (program : CCalls.Events.Program E) (start : CCalls.Typed.State)
    (heap : Heap) (p : Address) (logger : Option Address) (logging : Bool)
    (path : Path program start heap p)
    (loggerValue : load heap (p.member "logger") = some (.pointer logger))
    (loggingValue : load heap (p.member "logging") = some (boolean logging))
    (disabled : logger = none ∨ logging = false) (behavior) :
    (CCalls.Events.machine program).Behaves start behavior ↔
      behavior = .terminates [] ⟨.integer 2, heap⟩ := by
  obtain ⟨env, types, rest, reached, instanceValue, statusValue⟩ := path
  rw [CCalls.Events.internal_prefix_behaviors program reached behavior]
  exact Discard.suppressed_behaviors context TensorDerivativePreflight.message program env types rest heap p
    logger logging instanceValue statusValue loggerValue loggingValue disabled behavior

theorem logged (program : CCalls.Events.Program E) (start : CCalls.Typed.State)
    (heap : Heap) (p text category logger : Address) (environment : Option Address)
    (name : String) (foreign : CCalls.Events.External E) (path : Path program start heap p)
    (loggerValue : load heap (p.member "logger") = some (.pointer (some logger)))
    (loggingValue : load heap (p.member "logging") = some (.integer 1))
    (environmentValue : load heap (p.member "environment") = some (.pointer environment))
    (address : program.addresses logger = some name)
    (categoryBound : static.addresses "logStatus" = some category)
    (textBound : static.addresses TensorDerivativePreflight.message = some text)
    (external : program.externals name = some foreign) (prototype : foreign.signature = Logging.signature name)
    (behavior) :
    (CCalls.Events.machine program).Behaves start behavior ↔
      (∃ events value after, foreign.execute (Discard.arguments environment category text) heap events value after ∧
        behavior = .terminates events ⟨.integer 2, after⟩) ∨
      ((∀ events value after, ¬ foreign.execute (Discard.arguments environment category text) heap events value after) ∧
        behavior = .wrong []) := by
  obtain ⟨env, types, rest, reached, instanceValue, statusValue⟩ := path
  rw [CCalls.Events.internal_prefix_behaviors program reached behavior]
  exact Discard.logged_behaviors context TensorDerivativePreflight.message program env types rest heap p text
    category logger environment name foreign instanceValue statusValue loggerValue loggingValue environmentValue
    address categoryBound textBound external prototype behavior

/-- Mandatory numerical-failure obligations for the exact checked entry. -/
structure Contract (shape : Tensor.Shape) (hasOutput : Bool) : Prop where
  outcomes : ∀ state input : Values shape,
    (Solve.Tensor.Numerical.allFiniteBits (MultiplicationTotal.result input input) = true ∧
      (∃ result, Solve.Tensor.Finite.Executes (ArrayProfile.squareProgram shape)
        (ArrayProfile.environment state input) result) ∧
      ∀ k : Fin shape.volume, Binary64.Adds input[k] input[k]
        (.finite (SquareDiagonal.doubled input)[k])) ∨
    (Solve.Tensor.Numerical.allFiniteBits (MultiplicationTotal.result input input) = false ∧
      ∃ k : Fin shape.volume,
        Binary64.overflowValue ≤ Binary64.value input[k] * Binary64.value input[k])
  entry : ∀ {E : Type} (program : CCalls.Events.Program E)
    (heap : Heap) (p buffer : Address) (count : UInt64) (kind : Kind) (mode : Mode)
    (input : Values shape) (_matched : count.toNat = shape.volume) (_bounded : shape.volume < 2 ^ 64)
    (_defined : program.internal.definitions "fmi3GetContinuousStateDerivatives" =
      some (.tree (derivCheckedFunction shape hasOutput)))
    (_kindValue : load heap (p.member "kind") = some (.integer kind.code))
    (_modeValue : load heap (p.member "mode") = some (.integer mode.code))
    (_allowed : Reference.Allowed .getDerivatives kind mode)
    (_readable : Reads heap (p.member inputName) input)
    (_overflow : ∃ k : Fin shape.volume,
      Binary64.overflowValue ≤ Binary64.value input[k] * Binary64.value input[k]),
    Path program (.calling "fmi3GetContinuousStateDerivatives"
      (DerivativeCalls.values (some p) (some buffer) count) heap .done) heap p

  suppressed : ∀ {E : Type} (program : CCalls.Events.Program E) (start : CCalls.Typed.State)
    (heap : Heap) (p : Address) (logger : Option Address) (logging : Bool)
    (_path : Path program start heap p)
    (_loggerValue : load heap (p.member "logger") = some (.pointer logger))
    (_loggingValue : load heap (p.member "logging") = some (boolean logging))
    (_disabled : logger = none ∨ logging = false) (behavior),
    (CCalls.Events.machine program).Behaves start behavior ↔
      behavior = .terminates [] ⟨.integer 2, heap⟩

  logged : ∀ {E : Type} (program : CCalls.Events.Program E) (start : CCalls.Typed.State)
    (heap : Heap) (p text category logger : Address) (environment : Option Address)
    (name : String) (foreign : CCalls.Events.External E) (_path : Path program start heap p)
    (_loggerValue : load heap (p.member "logger") = some (.pointer (some logger)))
    (_loggingValue : load heap (p.member "logging") = some (.integer 1))
    (_environmentValue : load heap (p.member "environment") = some (.pointer environment))
    (_address : program.addresses logger = some name)
    (_categoryBound : static.addresses "logStatus" = some category)
    (_textBound : static.addresses TensorDerivativePreflight.message = some text)
    (_external : program.externals name = some foreign) (_prototype : foreign.signature = Logging.signature name)
    (behavior),
    (CCalls.Events.machine program).Behaves start behavior ↔
      (∃ events value after, foreign.execute (Discard.arguments environment category text) heap events value after ∧
        behavior = .terminates events ⟨.integer 2, after⟩) ∨
      ((∀ events value after, ¬ foreign.execute (Discard.arguments environment category text) heap events value after) ∧
        behavior = .wrong [])

theorem contract (shape : Tensor.Shape) (hasOutput : Bool) : Contract shape hasOutput where
  outcomes := outcomes_total
  entry program := public_prefix program shape hasOutput
  suppressed := suppressed
  logged := logged


end Rumoca.FMI3.TensorDerivativeDiscard
