import RumocaFMI3.Logging
import RumocaFMI3.FactoryPrefixCode

/-! Creation failures before an instance exists. The emitted logging branch
is executed in the shared C machine. All represented host outcomes and their
memory effects remain visible; no successful callback is a premise. -/
noncomputable section
namespace Rumoca.FMI3.FactoryRejection
open CTree CMemory CBody
variable [interface : CInterface]

theorem identity_guard (program : CCalls.Events.Program E) (rest : List Stmt)
    (env : Locals) (types : CLoops.Types) (heap : Heap)
    (stack : CCalls.Typed.Continuation) (valid : Bool)
    (bound : resolve env "validIdentity" = some (boolean valid)) :
    CCalls.Events.internalNext program
      (.body (.running (FactoryPrefix.identityGuard :: rest) env types heap) "fmi3Instance" stack) =
      some (.body (.running
        ((if valid then [] else code "Invalid name or instantiation token") ++
          rest) env types heap) "fmi3Instance" stack) := by
  cases valid <;>
    simp [CCalls.Events.internalNext, CCalls.Events.internalNextWith, CCalls.Typed.nextWithExpressions, FactoryPrefix.identityGuard,
      code, logCall, CLoops.nextWith, CLoops.noDeclarations, CLoops.evalWith, CBody.legacyExpressions,
      CBody.eval, CBody.evalWith,
      bound, boolean, Value.truth]

theorem dispatch (program : CCalls.Events.Program E) (message : String)
    (env : Locals) (types : CLoops.Types) (heap : Heap) (rest : List Stmt)
    (stack : CCalls.Typed.Continuation) (logger : Option Address) (logging : Bool)
    (loggerBound : resolve env "logMessage" = some (.pointer logger))
    (loggingBound : resolve env "loggingOn" = some (boolean logging)) :
    CCalls.Events.internalNext program
      (.body (.running (code message ++ rest) env types heap) "fmi3Instance" stack) =
      some (.body (.running
        ((if logger.isSome && logging then [logCall message] else []) ++
          Runtime.ret (Runtime.v "NULL") :: rest) env types heap) "fmi3Instance" stack) := by
  cases logger <;> cases logging <;>
    simp [CCalls.Events.internalNext, CCalls.Events.internalNextWith, CCalls.Typed.nextWithExpressions, code, logCall,
      CLoops.nextWith, CLoops.noDeclarations, CLoops.evalWith, CBody.legacyExpressions,
      Runtime.v, Runtime.ret, CBody.eval, CBody.evalWith, loggerBound, loggingBound, boolean, Value.truth]

theorem return_null (program : CCalls.Events.Program E) (env : Locals)
    (types : CLoops.Types) (heap : Heap) (rest : List Stmt)
    (stack : CCalls.Typed.Continuation)
    (nullBound : resolve env "NULL" = some (.pointer none))
    (handle : interface.types "fmi3Instance" = some .pointer) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (Runtime.ret (Runtime.v "NULL") :: rest) env types heap) "fmi3Instance" stack)
      (.returning (.pointer none) heap stack) := by
  refine .next (t := .body (.returned ⟨.pointer none, heap⟩) "fmi3Instance" stack) ?_ ?_
  · simp [CCalls.Events.internalNext, CCalls.Events.internalNextWith, CCalls.Typed.nextWithExpressions, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions,
      Runtime.ret, Runtime.v, CBody.eval, CBody.evalWith, nullBound]
  · exact .next (by simp [CCalls.Events.internalNext, CCalls.Events.internalNextWith, CCalls.Typed.nextWithExpressions,
      CCalls.returnCast, CBody.cast, handle, convert]) (.refl _)

theorem callback_entry (program : CCalls.Events.Program E) (message : String)
    (env : Locals) (types : CLoops.Types) (heap : Heap) (rest : List Stmt)
    (stack : CCalls.Typed.Continuation) (logger category text : Address)
    (environment : Option Address) (name : String)
    (loggerBound : env "logMessage" = some (.pointer (some logger)))
    (environmentBound : resolve env "instanceEnvironment" = some (.pointer environment))
    (errorBound : resolve env "fmi3Error" = some (.integer 3))
    (categoryBound : interface.literals "logStatus" = some category)
    (messageBound : interface.literals message = some text)
    (address : program.addresses logger = some name) :
    CCalls.Events.internalNext program
      (.body (.running (logCall message :: rest) env types heap) "fmi3Instance" stack) =
      some (.calling name (Logging.arguments environment category text) heap
        (.caller .discard rest env types "fmi3Instance" stack)) := by
  have resolved : CCalls.Events.resolve program env heap (Runtime.v "logMessage") = some name := by
    simp [CCalls.Events.resolve, CCalls.Events.resolveWith, CCalls.Indirect.resolveWith, CBody.legacyExpressions, Runtime.v, CBody.resolve, loggerBound,
      CCalls.Indirect.valueTarget, address, CBody.eval, CBody.evalWith]
  have values : CCalls.arguments env heap
      [Runtime.v "instanceEnvironment", Runtime.v "fmi3Error", .str "logStatus", .str message] =
      some (Logging.arguments environment category text) := by
    simp [CCalls.arguments, CCalls.argumentsWith, CBody.legacyExpressions, Runtime.v, CBody.eval, CBody.evalWith, environmentBound, errorBound,
      categoryBound, messageBound, Logging.arguments]
  have blocked : CLoops.next (.running (logCall message :: rest) env types heap) = none := by
    simp [CLoops.next, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions, logCall, CBody.eval, CBody.evalWith]
  simp only [Runtime.v] at resolved values
  simp only [CCalls.Events.internalNext, CCalls.Events.internalNextWith, CCalls.Typed.nextWithExpressions, blocked]
  simp [CCalls.Events.enterCallWith, logCall, CCalls.Indirect.operand, resolved, values]

theorem silent_equivalence (program : CCalls.Events.Program E) (message : String)
    (env : Locals) (types : CLoops.Types) (heap : Heap) (rest : List Stmt)
    (stack : CCalls.Typed.Continuation) (logger : Option Address) (logging : Bool)
    (loggerBound : resolve env "logMessage" = some (.pointer logger))
    (loggingBound : resolve env "loggingOn" = some (boolean logging))
    (nullBound : resolve env "NULL" = some (.pointer none))
    (handle : interface.types "fmi3Instance" = some .pointer)
    (quiet : (logger.isSome && logging) = false) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.body (.running (code message ++ rest) env types heap) "fmi3Instance" stack) behavior ↔
    (CCalls.Events.machine program).Behaves (.returning (.pointer none) heap stack) behavior := by
  have first := dispatch program message env types heap rest stack logger logging loggerBound loggingBound
  rw [quiet] at first
  simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append] at first
  exact CCalls.Events.internal_prefix_behaviors program
    (.next first (return_null program env types heap rest stack nullBound handle)) behavior

/-- The callback may produce any permitted event trace and writable-memory
effect. If it has no represented outcome, this external-call model is stuck.
Native callback divergence/reentrancy require their own host refinement. -/
theorem all_behaviors (program : CCalls.Events.Program E) (message : String)
    (env : Locals) (types : CLoops.Types) (heap : Heap) (rest : List Stmt)
    (logger category text : Address) (environment : Option Address)
    (name : String) (foreign : CCalls.Events.External E)
    (loggerBound : env "logMessage" = some (.pointer (some logger)))
    (loggingBound : resolve env "loggingOn" = some (boolean true))
    (environmentBound : resolve env "instanceEnvironment" = some (.pointer environment))
    (errorBound : resolve env "fmi3Error" = some (.integer 3))
    (nullBound : resolve env "NULL" = some (.pointer none))
    (categoryBound : interface.literals "logStatus" = some category)
    (messageBound : interface.literals message = some text)
    (address : program.addresses logger = some name)
    (external : program.externals name = some foreign)
    (prototype : foreign.signature = Logging.signature name)
    (handle : interface.types "fmi3Instance" = some .pointer)
    (converted : CCalls.Events.convertedArguments (Logging.signature name).parameters
      (Logging.arguments environment category text) = some (Logging.arguments environment category text))
    (behavior) :
    (CCalls.Events.machine program).Behaves
      (.body (.running (code message ++ rest) env types heap) "fmi3Instance" .done) behavior ↔
    (∃ events value after, foreign.execute (Logging.arguments environment category text)
      heap events value after ∧ behavior = .terminates events ⟨.pointer none, after⟩) ∨
    ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category text)
      heap events value after) ∧ behavior = .wrong []) := by
  have first := dispatch program message env types heap rest .done (some logger) true
    (by simp [resolve, loggerBound]) loggingBound
  simp only [Option.isSome_some, Bool.and_self, ↓reduceIte, List.singleton_append] at first
  have path := Transition.Reaches.next
    (step := fun s t => CCalls.Events.internalNext program s = some t) first
    (.next (callback_entry program message env types heap (Runtime.ret (Runtime.v "NULL") :: rest)
      .done logger category text environment name loggerBound environmentBound errorBound
      categoryBound messageBound address) (.refl _))
  rw [CCalls.Events.internal_prefix_behaviors program path behavior]
  apply CCalls.Events.external_choices_behaviors program external
    (prototype ▸ converted)
    (fun _ after => ⟨.pointer none, after⟩)
  intro events value after executed
  apply CCalls.Events.internal_prefix program (.next (by rfl)
    (return_null program env types after rest .done nullBound handle))
  exact CCalls.Events.return_forced program (.pointer none) after

end Rumoca.FMI3.FactoryRejection
