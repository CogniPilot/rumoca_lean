import RumocaFMI3.ErrorBodies
import RumocaC.LiteralPointers
import RumocaC.LoopProofs

/-! Ordinary entry and return for the actual failure helper, followed by a
complete rejected public call. Literal addresses and function definitions are
supplied explicitly. Enabled foreign logging and actual adapter-byte binding
require separate contracts. -/
noncomputable section
namespace Rumoca.FMI3.ErrorCalls
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses
open CTree CMemory CBody LifecycleBodies

def failureEnv (p message : Address) : Locals :=
  CBody.bind (CBody.bind (fun _ => none) "message" (.pointer (some message))) "m" (.pointer (some p))

theorem failure_parameters (p message : Address) :
    CCalls.parameters Runtime.helpers[0].signature.parameters
      [.pointer (some p), .pointer (some message)] = some (failureEnv p message) := by
  rfl

/-- Complete failure-helper entry, disabled-logging execution and ordinary
return under any caller continuation. Only the instance's mode cell changes. -/
theorem failure_reaches (program : CCalls.Program) (heap : Heap) (p message : Address)
    (old : Option Value) (logger : Option Address) (stack : CCalls.Typed.Continuation)
    (defined : program.definitions "fail" = some (.tree Runtime.helpers[0]))
    (hm : heap (p.member "mode") = some ⟨.int32, true, old⟩)
    (hl : load heap (p.member "logger") = some (.pointer logger))
    (hg : load heap (p.member "logging") = some (.integer 0)) :
    Transition.Reaches (CCalls.Typed.machine program).step
      (.calling "fail" [.pointer (some p), .pointer (some message)] heap stack)
      (.returning (.integer 3) (writeMode heap p .terminated) stack) := by
  apply CBodyEmbedding.typed_call_reaches program Runtime.helpers[0]
    [.pointer (some p), .pointer (some message)] (failureEnv p message) heap
    ⟨.integer 3, writeMode heap p .terminated⟩ (.integer 3) stack 3
  · exact defined
  · exact failure_parameters p message
  · exact BodyEmbedding.helpers_closed _ (by simp [Runtime.helpers])
  · exact ErrorBodies.failure_silent_run _ heap p old logger
      (by simp [failureEnv, CBody.bind, resolve]) hm hl hg
      (by simp [failureEnv, CBody.bind, resolve, constants])
  · simp [Runtime.helpers, CCalls.returnCast, CBody.cast, convert]

/-- Shared execution of the emitted `return fail(m, message)` statement.
Every rejected API can reuse this ordinary-call proof with its own prefix. -/
theorem failure_statement_reaches (program : CCalls.Program) (env : Locals)
    (types : CLoops.Types) (heap : Heap) (p message : Address) (text : String)
    (rest : List Stmt) (old : Option Value) (logger : Option Address)
    (stack : CCalls.Typed.Continuation)
    (helper : program.definitions "fail" = some (.tree Runtime.helpers[0]))
    (unshadowed : env "fail" = none)
    (hp : resolve env "m" = some (.pointer (some p)))
    (literal : static.addresses text = some message)
    (hm : heap (p.member "mode") = some ⟨.int32, true, old⟩)
    (hl : load heap (p.member "logger") = some (.pointer logger))
    (hg : load heap (p.member "logging") = some (.integer 0)) :
    Transition.Reaches (CCalls.Typed.machine program).step
      (.body (.running (Runtime.fail text :: rest) env types heap) "fmi3Status" stack)
      (.returning (.integer 3) (writeMode heap p .terminated) stack) := by
  let saved := CCalls.Typed.Continuation.caller .ret rest env types "fmi3Status" stack
  refine .next ?_ ((failure_reaches program heap p message old logger saved helper hm hl hg).trans ?_)
  · simp [CCalls.Typed.machine, CCalls.Typed.machineWith, CCalls.Typed.nextIn, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions,
      CCalls.Typed.enterCallWith, CCalls.callOperand, CCalls.argumentsWith, CBody.legacyExpressions, Runtime.fail,
      Runtime.ret, Runtime.call, Runtime.v, CBody.eval, CBody.evalWith, hp, unshadowed, literal, saved, CCalls.Typed.nextWithExpressions]
  · exact .next (by simp [CCalls.Typed.machine, CCalls.Typed.machineWith, CCalls.Typed.nextIn, CCalls.Typed.resumeWith, CBody.legacyExpressions,
      saved, CCalls.returnCast, CBody.cast, convert, CCalls.Typed.nextWithExpressions]) (.refl _)

/-- Shared public-call plumbing for a prefix reaching the ordinary failure
helper. Each API proves its own prefix; this theorem supplies fresh entry,
typed execution, helper dispatch and return under any saved caller. -/
theorem failure_after_prefix (m : Solve.FMI3Model source) (sig : Signature)
    (status : sig.result = "fmi3Status") (program : CCalls.Program)
    (args : List Value) (env env' : Locals) (heap heap' : Heap) (n : Nat)
    (p message : Address) (text : String) (tail : List Stmt) (old : Option Value)
    (logger : Option Address) (stack : CCalls.Typed.Continuation)
    (defined : program.definitions sig.name = some (.tree (Runtime.function m sig)))
    (bound : CCalls.parameters sig.parameters args = some env)
    (executed : run n (.running (Runtime.body m sig) env heap) =
      some (.running (Runtime.fail text :: tail) env' heap'))
    (helper : program.definitions "fail" = some (.tree Runtime.helpers[0]))
    (unshadowed : env' "fail" = none)
    (instanceBound : resolve env' "m" = some (.pointer (some p)))
    (literal : static.addresses text = some message)
    (hm : heap' (p.member "mode") = some ⟨.int32, true, old⟩)
    (hl : load heap' (p.member "logger") = some (.pointer logger))
    (hg : load heap' (p.member "logging") = some (.integer 0)) :
    Transition.Reaches (CCalls.Typed.machine program).step
      (.calling sig.name args heap stack)
      (.returning (.integer 3) (LifecycleBodies.writeMode heap' p .terminated) stack) := by
  obtain ⟨types, typeBindings, _⟩ := CCalls.Parameters.parameters_typed _ _ _ bound
  obtain ⟨types', typed, _⟩ := CBodyEmbedding.run_refines n
    (.running (Runtime.body m sig) env heap) _ types (BodyEmbedding.body_closed m sig) executed
  have entry := CCalls.Typed.tree_entry program sig.name args heap stack
    (Runtime.function m sig) env types defined bound typeBindings
  have reached := CCalls.Typed.body_reaches program (CLoops.run_reaches typed) sig.result stack
  have steps := Transition.Reaches.next (step := (CCalls.Typed.machine program).step) entry reached
  rw [status] at steps
  exact steps.trans (ErrorCalls.failure_statement_reaches program env' types' heap' p message
    text tail old logger stack helper unshadowed instanceBound literal hm hl hg)

def nominalSignature : Signature :=
  ⟨"fmi3Status", "fmi3GetNominalsOfContinuousStates",
    [⟨"fmi3Instance", "instance", false⟩,
     ⟨"fmi3Float64", "nominals", true⟩,
     ⟨"size_t", "nContinuousStates", false⟩]⟩

def nominalArguments (p : Address) (buffer : Option Address) (count : UInt64) : List Value :=
  [.pointer (some p), .pointer buffer, .integer count.toNat]

def nominalEnv (p : Address) (buffer : Option Address) (count : UInt64) : Locals :=
  CBody.bind (CBody.bind (CBody.bind (fun _ => none) "nContinuousStates" (.integer count.toNat))
    "nominals" (.pointer buffer)) "instance" (.pointer (some p))

theorem nominal_parameters (p : Address) (buffer : Option Address) (count : UInt64) :
    CCalls.parameters nominalSignature.parameters (nominalArguments p buffer count) =
      some (nominalEnv p buffer count) := by
  have converted : CBody.cast "size_t" (.integer count.toNat) =
      some (.integer count.toNat) :=
    CLoops.Calls.cast_of_type "size_t" .size _ _ (by rfl)
      (CLoops.convert_size_nat _ count.toNat_lt_size)
  simp only [nominalSignature, nominalArguments, CCalls.parameters,
    CCalls.parameterType, Bool.false_eq_true, ↓reduceIte, converted]
  rfl

def rejectionMessage : String := "Call is not allowed in the current FMI state"

def nominalRest : List Stmt :=
  Runtime.scalarAccessCheck "nominals" "nContinuousStates" ++
    [.assign (.index (Runtime.v "nominals") (Runtime.n 0)) (Runtime.n 1), Runtime.ok]

/-- The public call binds its actual parameters, rejects Instantiated before
any output-pointer dereference, executes the ordinary failure helper and
returns Error. The output pointer may be null; only the mode cell changes. -/
theorem nominal_reject_reaches (m : Solve.FMI3Model source) (program : CCalls.Program)
    (heap : Heap) (p message : Address) (buffer : Option Address) (count : UInt64)
    (kind : Kind) (logger : Option Address) (stack : CCalls.Typed.Continuation)
    (defined : program.definitions nominalSignature.name =
      some (.tree (Runtime.function m nominalSignature)))
    (helper : program.definitions "fail" = some (.tree Runtime.helpers[0]))
    (literal : static.addresses rejectionMessage = some message)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer Mode.instantiated.code)⟩)
    (hl : load heap (p.member "logger") = some (.pointer logger))
    (hg : load heap (p.member "logging") = some (.integer 0)) :
    Transition.Reaches (CCalls.Typed.machine program).step
      (.calling nominalSignature.name (nominalArguments p buffer count) heap stack)
      (.returning (.integer 3) (writeMode heap p .terminated) stack) := by
  simp only [rejectionMessage] at literal
  obtain ⟨types, ht, _⟩ := CCalls.Parameters.parameters_typed _ _ _
    (nominal_parameters p buffer count)
  obtain ⟨types', rejected⟩ := ErrorBodies.nominals_reject_reaches m nominalSignature rfl
    program (nominalEnv p buffer count) types heap p kind stack
    (by simp [nominalEnv, CBody.bind]) (by simp [nominalEnv, CBody.bind]) hk
    (by simp [load, hm, convert, Mode.code])
  have entry := CCalls.Typed.tree_entry program nominalSignature.name
    (nominalArguments p buffer count) heap stack (Runtime.function m nominalSignature)
    (nominalEnv p buffer count) types defined (nominal_parameters p buffer count) ht
  refine (Transition.Reaches.next (step := (CCalls.Typed.machine program).step) entry rejected).trans ?_
  exact failure_statement_reaches program
    (CBody.bind (nominalEnv p buffer count) "m" (.pointer (some p))) types' heap p message
    rejectionMessage nominalRest _ logger stack helper
    (by simp [nominalEnv, CBody.bind]) (by simp [CBody.bind, resolve]) literal hm hl hg

/-- All behaviors of the complete public call have the same error result and
whole-heap frame. Supplied literal objects survive the call unchanged. -/
theorem nominal_reject_correct (m : Solve.FMI3Model source) (program : CCalls.Program)
    (heap : Heap) (p message : Address) (buffer : Option Address) (count : UInt64)
    (kind : Kind) (logger : Option Address) (signed : Bool)
    (defined : program.definitions nominalSignature.name =
      some (.tree (Runtime.function m nominalSignature)))
    (helper : program.definitions "fail" = some (.tree Runtime.helpers[0]))
    (literal : static.addresses rejectionMessage = some message)
    (stored : CLiteral.Stored signed heap message rejectionMessage)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer Mode.instantiated.code)⟩)
    (hl : load heap (p.member "logger") = some (.pointer logger))
    (hg : load heap (p.member "logging") = some (.integer 0)) :
    (∀ behavior, (CCalls.Typed.machine program).Behaves
      (.calling nominalSignature.name (nominalArguments p buffer count) heap .done) behavior ↔
      behavior = .terminates ⟨.integer 3, writeMode heap p .terminated⟩) ∧
    (∀ q, q ≠ p.member "mode" → writeMode heap p .terminated q = heap q) ∧
    CLiteral.Stored signed (writeMode heap p .terminated) message rejectionMessage := by
  have reaches := nominal_reject_reaches m program heap p message buffer count kind logger
    .done defined helper literal hk hm hl hg
  exact ⟨fun behavior => (CCalls.Typed.machine program).behavior_iff
      (reaches.trans (.next rfl (.refl _))) rfl,
    fun q hq => write_frame heap p q .terminated hq,
    CLiteral.Stored.after_steps stored reaches⟩

end Rumoca.FMI3.ErrorCalls
