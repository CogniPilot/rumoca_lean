import RumocaFMI3.DebugLoggingLoop
import RumocaFMI3.StaticErrorCalls

/-! Category failures compose the actual shared failure helper. Its contract
retains every foreign logging outcome, including a blocked callback. Validation
does not select a comparison result or assume logging terminates. -/
noncomputable section
namespace Rumoca.FMI3.DebugLogging
open CTree CMemory CBody CLoops CStringMemory CStringOperations

structure FailureContract [CInterface] (program : CCalls.Events.Program E)
    (heap : Heap) (handle : Address) (text : String)
    (outcomes : Transition.Events.Observation E CBody.Result → Prop) : Prop where
  body : ∀ (env : Locals) (types : Types) (rest : List Stmt),
    env "fail" = none → resolve env "m" = some (.pointer (some handle)) → ∀ behavior,
    (CCalls.Events.machine program).Behaves
      (.body (.running (failure text :: rest) env types heap) "fmi3Status" .done) behavior ↔
    outcomes behavior

theorem suppressed_failure_contract {E : Type} (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p message : Address)
      (text : String) (old : Option Value) (logger : Option Address) (logging : Bool),
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals text = some message →
      heap (p.member "mode") = some ⟨.int32, true, old⟩ →
      load heap (p.member "logger") = some (.pointer logger) →
      load heap (p.member "logging") = some (boolean logging) →
      (logger = none ∨ logging = false) →
      FailureContract program heap p text
        (fun behavior => behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩) := by
  letI : CInterface := context.target
  intro program heap p message text old logger logging helper literal hm hl hg suppressed
  constructor
  intro env types rest unshadowed instanceBound behavior
  exact StaticErrors.statement_suppressed_behaviors context program env types rest text heap p message
    old logger logging unshadowed instanceBound helper literal hm hl hg suppressed behavior

theorem logged_failure_contract {E : Type} (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p message category logger : Address)
      (text : String) (environment : Option Address) (old : Option Value)
      (name : String) (foreign : CCalls.Events.External E),
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals text = some message → program.addresses logger = some name →
      program.externals name = some foreign → foreign.signature = Logging.signature name →
      literals "logStatus" = some category →
      heap (p.member "mode") = some ⟨.int32, true, old⟩ →
      load heap (p.member "logger") = some (.pointer (some logger)) →
      load heap (p.member "logging") = some (.integer 1) →
      load heap (p.member "environment") = some (.pointer environment) →
      FailureContract program heap p text (fun behavior =>
        (∃ events value final, foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode heap p .terminated) events value final ∧
          behavior = .terminates events ⟨.integer 3, final⟩) ∨
        ((∀ events value final, ¬ foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode heap p .terminated) events value final) ∧ behavior = .wrong [])) := by
  letI : CInterface := context.target
  intro program heap p message category logger text environment old name foreign helper messageBound
    address external prototype literal hm hl hg he
  constructor
  intro env types rest unshadowed instanceBound behavior
  exact StaticErrors.statement_all_behaviors context program env types rest text heap p message category
    logger environment old name foreign unshadowed instanceBound helper messageBound address external
    prototype literal hm hl hg he behavior

variable [interface : CInterface]

theorem iteration_invalid_behaviors (program : CCalls.Events.Program E)
    (env : Locals) (types : Types) (heap : Heap) (p expected : Address) (selected : Option Address)
    (bytes expectedBytes : List UInt8) (old : Value) (rest : List Stmt)
    (pointer : interface.types "const char *" = some .pointer)
    (integer : interface.types "int" = some .int32)
    (present : env "difference" = some old) (typed : types "difference" = some .int32)
    (unshadowed : env "strcmp" = none) (named : interface.constants "strcmp" = none)
    (bound : program.externals "strcmp" = some (CStringCalls.compareExternal integer))
    (loaded : CBody.eval env heap category = some (.pointer selected))
    (literal : interface.literals "logStatus" = some expected)
    (selectedStored : ∀ value, selected = some value → Contents heap value bytes)
    (expectedStored : Contents heap expected expectedBytes)
    (invalid : ¬ Accepted selected bytes expectedBytes)
    (failureName : env "fail" = none)
    (instanceBound : resolve env "m" = some (.pointer (some p)))
    (outcomes : Transition.Events.Observation E CBody.Result → Prop)
    (failed : FailureContract program heap p "Unknown log category" outcomes)
    (behavior) :
    (CCalls.Events.machine program).Behaves
      (.body (.running (iteration ++ rest) env types heap) "fmi3Status" .done) behavior ↔
    outcomes behavior := by
  have first := null_category_step env types heap selected (comparison :: rejectDifference :: rest) loaded
  apply (CCalls.Events.internal_prefix_behaviors program
    (.next (CCalls.Events.body_step program first "fmi3Status" .done) (.refl _)) behavior).trans
  cases selected with
  | none =>
    exact failed.body env types (comparison :: rejectDifference :: rest) failureName instanceBound behavior
  | some selected =>
    have different : bytes ≠ expectedBytes := fun same => invalid ⟨rfl, same⟩
    apply Iff.trans (b := (CCalls.Events.machine program).Behaves
      (.body (.running (failure "Unknown log category" :: rest) env types heap) "fmi3Status" .done) behavior)
    · apply CStringCalls.compare_assignment_equivalence program env types heap "difference"
        [category, .str "logStatus"] (rejectDifference :: rest) "fmi3Status" .done old
        selected expected bytes expectedBytes pointer integer present typed unshadowed named bound
        (by simp [CCalls.arguments, CCalls.argumentsWith, CBody.legacyExpressions, loaded, CBody.eval, CBody.evalWith, literal]) (selectedStored selected rfl) expectedStored
      intro value range compared observed
      have nonzero : value ≠ 0 := fun zero => different ((comparison_zero compared).mp zero)
      have step := difference_step (CBody.bind env "difference" (.integer value)) types heap value rest
        (by simp [CBody.bind])
      rw [if_neg nonzero] at step
      apply (CCalls.Events.internal_prefix_behaviors program
        (.next (CCalls.Events.body_step program step "fmi3Status" .done) (.refl _)) observed).trans
      exact (failed.body (CBody.bind env "difference" (.integer value)) types rest
        (by simp [CBody.bind, failureName]) (by simpa [resolve, CBody.bind] using instanceBound)
        observed).trans (failed.body env types rest failureName instanceBound observed).symm
    · exact failed.body env types rest failureName instanceBound behavior

end Rumoca.FMI3.DebugLogging
end
