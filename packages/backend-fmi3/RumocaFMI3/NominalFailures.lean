import RumocaFMI3.Nominals
import RumocaFMI3.LoggingStatements
import RumocaC.LiteralCollection

/-! Nominal-query lifecycle and access failures, with exact enabled or disabled
logging behavior. The two failure reasons and successful/null cases cover all arguments. -/
noncomputable section
namespace Rumoca.FMI3.Nominals
open CTree CMemory CBody CLiteral

section
variable [static : StaticLiterals]
private local instance prefixInterface : CInterface := cInterface static.addresses

theorem reject_dispatch (model : Solve.FMI3Model source)
    (program : CCalls.Events.Program E) (heap : Heap) (p : Address) (buffer : Option Address)
    (count : UInt64) (kind : Kind) (mode : Mode) (stack : CCalls.Typed.Continuation)
    (defined : program.internal.definitions ErrorCalls.nominalSignature.name =
      some (.tree (Runtime.function model ErrorCalls.nominalSignature)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (rejected : ¬ Reference.Allowed .getNominals kind mode) :
    ∃ types, Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.calling ErrorCalls.nominalSignature.name (ErrorCalls.nominalArguments p buffer count) heap stack)
      (.body (.running (Runtime.fail ErrorCalls.rejectionMessage :: ErrorCalls.nominalRest)
        (CBody.bind (ErrorCalls.nominalEnv p buffer count) "m" (.pointer (some p))) types heap)
        "fmi3Status" stack) := by
  let env := ErrorCalls.nominalEnv p buffer count
  have params := ErrorCalls.nominal_parameters p buffer count
  obtain ⟨types, boundTypes, _⟩ := CCalls.Parameters.parameters_typed _ _ _ params
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have dispatched := LifecycleGuard.reject_prefix env heap p .getNominals kind mode
    ErrorCalls.nominalRest (by simp [env, ErrorCalls.nominalEnv, CBody.bind])
    (by simp [env, ErrorCalls.nominalEnv, CBody.bind]) hk modeLoaded rejected
  have body : Runtime.body model ErrorCalls.nominalSignature =
      Runtime.require .getNominals ++ ErrorCalls.nominalRest := by
    simp [Runtime.body, ErrorCalls.nominalSignature, ErrorCalls.nominalRest]
  rw [← body] at dispatched
  obtain ⟨types', dispatched', _⟩ := CBodyEmbedding.run_refines 3
    (.running (Runtime.body model ErrorCalls.nominalSignature) env heap) _ types
    (BodyEmbedding.body_closed model ErrorCalls.nominalSignature) dispatched
  exact ⟨types', Transition.Reaches.next
    (step := fun s t => CCalls.Events.internalNext program s = some t)
    (CCalls.Events.tree_entry program ErrorCalls.nominalSignature.name
      (ErrorCalls.nominalArguments p buffer count) heap stack
      (Runtime.function model ErrorCalls.nominalSignature) env types defined params boundTypes)
    (CCalls.Events.body_reaches program (CLoops.run_reaches dispatched') "fmi3Status" stack)⟩

theorem reject_all_behaviors (model : Solve.FMI3Model source)
    (program : CCalls.Events.Program E) (heap : Heap)
    (p message category logger : Address) (environment buffer : Option Address)
    (count : UInt64) (kind : Kind) (mode : Mode) (name : String) (foreign : CCalls.Events.External E)
    (defined : program.internal.definitions ErrorCalls.nominalSignature.name =
      some (.tree (Runtime.function model ErrorCalls.nominalSignature)))
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (messageBound : static.addresses ErrorCalls.rejectionMessage = some message)
    (address : program.addresses logger = some name)
    (external : program.externals name = some foreign)
    (prototype : foreign.signature = Logging.signature name)
    (literal : static.addresses "logStatus" = some category)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (hl : load heap (p.member "logger") = some (.pointer (some logger)))
    (hg : load heap (p.member "logging") = some (.integer 1))
    (he : load heap (p.member "environment") = some (.pointer environment))
    (rejected : ¬ Reference.Allowed .getNominals kind mode) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling ErrorCalls.nominalSignature.name (ErrorCalls.nominalArguments p buffer count) heap .done) behavior ↔
      (∃ events value after, foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) events value after ∧
        behavior = .terminates events ⟨.integer 3, after⟩) ∨
      ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) events value after) ∧ behavior = .wrong []) := by
  obtain ⟨types, dispatched⟩ := reject_dispatch model program heap p buffer count kind mode .done
    defined hk hm rejected
  rw [CCalls.Events.internal_prefix_behaviors program dispatched behavior]
  exact Logging.failure_statement_all_behaviors program
    (CBody.bind (ErrorCalls.nominalEnv p buffer count) "m" (.pointer (some p))) types
    ErrorCalls.nominalRest ErrorCalls.rejectionMessage heap p message category logger environment
    _ name foreign helper (by simp [ErrorCalls.nominalEnv, CBody.bind])
    (by simp [CBody.bind, resolve]) messageBound address external prototype literal hm hl hg he behavior

theorem reject_silent_behaviors (model : Solve.FMI3Model source)
    (program : CCalls.Events.Program E) (heap : Heap) (p message : Address)
    (buffer logger : Option Address) (count : UInt64) (kind : Kind) (mode : Mode)
    (defined : program.internal.definitions ErrorCalls.nominalSignature.name =
      some (.tree (Runtime.function model ErrorCalls.nominalSignature)))
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (messageBound : static.addresses ErrorCalls.rejectionMessage = some message)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (hl : load heap (p.member "logger") = some (.pointer logger))
    (hg : load heap (p.member "logging") = some (.integer 0))
    (rejected : ¬ Reference.Allowed .getNominals kind mode) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling ErrorCalls.nominalSignature.name (ErrorCalls.nominalArguments p buffer count) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩ := by
  obtain ⟨types, dispatched⟩ := reject_dispatch model program heap p buffer count kind mode .done
    defined hk hm rejected
  rw [CCalls.Events.internal_prefix_behaviors program dispatched behavior]
  exact Logging.failure_statement_silent_behaviors program
    (CBody.bind (ErrorCalls.nominalEnv p buffer count) "m" (.pointer (some p))) types
    ErrorCalls.nominalRest ErrorCalls.rejectionMessage heap p message _ logger helper
    (by simp [ErrorCalls.nominalEnv, CBody.bind]) (by simp [CBody.bind, resolve]) messageBound hm hl hg behavior

def accessMessage : String := "Expected one continuous state"

def accessRest : List Stmt :=
  [.assign (.index (Runtime.v "nominals") (Runtime.n 0)) (Runtime.n 1), Runtime.ok]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem invalid_body (model : Solve.FMI3Model source) (heap : Heap) (p : Address)
    (buffer : Option Address) (count : UInt64) (kind : Kind) (mode : Mode)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getNominals kind mode)
    (invalid : count.toNat ≠ 1 ∨ buffer = none) :
    run 4 (.running (Runtime.body model ErrorCalls.nominalSignature)
      (ErrorCalls.nominalEnv p buffer count) heap) =
      some (.running (Runtime.fail accessMessage :: accessRest)
        (CBody.bind (ErrorCalls.nominalEnv p buffer count) "m" (.pointer (some p))) heap) := by
  have accepted := LifecycleGuard.accept (ErrorCalls.nominalEnv p buffer count)
    heap p .getNominals kind mode ErrorCalls.nominalRest
    (by simp [ErrorCalls.nominalEnv, CBody.bind]) (by simp [ErrorCalls.nominalEnv, CBody.bind]) hk hm allowed
  have body : Runtime.body model ErrorCalls.nominalSignature =
      Runtime.require .getNominals ++ ErrorCalls.nominalRest := by
    simp [Runtime.body, ErrorCalls.nominalSignature, ErrorCalls.nominalRest]
  rw [body, show 4 = 3 + 1 from rfl, run_add, accepted]
  rcases invalid with bad | rfl
  · simp [ErrorCalls.nominalRest, Runtime.scalarAccessCheck, Runtime.reject, Runtime.branch,
      Runtime.either, Runtime.nev, Runtime.negate, Runtime.v, Runtime.n, run, next, eval,
      ErrorCalls.nominalEnv, CBody.bind, resolve, constants, comparison, boolean, Value.truth,
      bad, accessMessage, accessRest]
  · simp [ErrorCalls.nominalRest, Runtime.scalarAccessCheck, Runtime.reject, Runtime.branch,
      Runtime.either, Runtime.nev, Runtime.negate, Runtime.v, Runtime.n, run, next, eval,
      ErrorCalls.nominalEnv, CBody.bind, resolve, constants, comparison, boolean, Value.truth,
      accessMessage, accessRest]

theorem invalid_dispatch (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (p : Address) (buffer : Option Address) (count : UInt64)
    (kind : Kind) (mode : Mode) (stack : CCalls.Typed.Continuation)
    (defined : program.internal.definitions ErrorCalls.nominalSignature.name =
      some (.tree (Runtime.function model ErrorCalls.nominalSignature)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getNominals kind mode)
    (invalid : count.toNat ≠ 1 ∨ buffer = none) :
    ∃ types, Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.calling ErrorCalls.nominalSignature.name (ErrorCalls.nominalArguments p buffer count) heap stack)
      (.body (.running (Runtime.fail accessMessage :: accessRest)
        (CBody.bind (ErrorCalls.nominalEnv p buffer count) "m" (.pointer (some p))) types heap) "fmi3Status" stack) := by
  exact CCalls.Events.body_prefix_reaches program (Runtime.function model ErrorCalls.nominalSignature)
    (ErrorCalls.nominalArguments p buffer count) (ErrorCalls.nominalEnv p buffer count)
    (CBody.bind (ErrorCalls.nominalEnv p buffer count) "m" (.pointer (some p))) heap heap
    (Runtime.fail accessMessage :: accessRest) stack 4 defined (ErrorCalls.nominal_parameters p buffer count)
    (BodyEmbedding.body_closed model ErrorCalls.nominalSignature)
    (invalid_body model heap p buffer count kind mode hk hm allowed invalid)

theorem invalid_all_behaviors (model : Solve.FMI3Model source)
    (program : CCalls.Events.Program E) (heap : Heap)
    (p message category logger : Address) (environment buffer : Option Address)
    (count : UInt64) (kind : Kind) (mode : Mode) (name : String) (foreign : CCalls.Events.External E)
    (defined : program.internal.definitions ErrorCalls.nominalSignature.name =
      some (.tree (Runtime.function model ErrorCalls.nominalSignature)))
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (messageBound : static.addresses accessMessage = some message)
    (address : program.addresses logger = some name)
    (external : program.externals name = some foreign)
    (prototype : foreign.signature = Logging.signature name)
    (literal : static.addresses "logStatus" = some category)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (hl : load heap (p.member "logger") = some (.pointer (some logger)))
    (hg : load heap (p.member "logging") = some (.integer 1))
    (he : load heap (p.member "environment") = some (.pointer environment))
    (allowed : Reference.Allowed .getNominals kind mode)
    (invalid : count.toNat ≠ 1 ∨ buffer = none) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling ErrorCalls.nominalSignature.name (ErrorCalls.nominalArguments p buffer count) heap .done) behavior ↔
      (∃ events value after, foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) events value after ∧
        behavior = .terminates events ⟨.integer 3, after⟩) ∨
      ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) events value after) ∧ behavior = .wrong []) := by
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  obtain ⟨types, dispatched⟩ := invalid_dispatch model program heap p buffer count kind mode .done
    defined hk modeLoaded allowed invalid
  rw [CCalls.Events.internal_prefix_behaviors program dispatched behavior]
  exact Logging.failure_statement_all_behaviors program
    (CBody.bind (ErrorCalls.nominalEnv p buffer count) "m" (.pointer (some p))) types accessRest accessMessage
    heap p message category logger environment _ name foreign helper
    (by simp [ErrorCalls.nominalEnv, CBody.bind]) (by simp [CBody.bind, resolve])
    messageBound address external prototype literal hm hl hg he behavior

theorem invalid_silent_behaviors (model : Solve.FMI3Model source)
    (program : CCalls.Events.Program E) (heap : Heap) (p message : Address)
    (buffer logger : Option Address) (count : UInt64) (kind : Kind) (mode : Mode)
    (defined : program.internal.definitions ErrorCalls.nominalSignature.name =
      some (.tree (Runtime.function model ErrorCalls.nominalSignature)))
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (messageBound : static.addresses accessMessage = some message)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (hl : load heap (p.member "logger") = some (.pointer logger))
    (hg : load heap (p.member "logging") = some (.integer 0))
    (allowed : Reference.Allowed .getNominals kind mode)
    (invalid : count.toNat ≠ 1 ∨ buffer = none) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling ErrorCalls.nominalSignature.name (ErrorCalls.nominalArguments p buffer count) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩ := by
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  obtain ⟨types, dispatched⟩ := invalid_dispatch model program heap p buffer count kind mode .done
    defined hk modeLoaded allowed invalid
  rw [CCalls.Events.internal_prefix_behaviors program dispatched behavior]
  exact Logging.failure_statement_silent_behaviors program
    (CBody.bind (ErrorCalls.nominalEnv p buffer count) "m" (.pointer (some p))) types accessRest accessMessage
    heap p message _ logger helper
    (by simp [ErrorCalls.nominalEnv, CBody.bind]) (by simp [CBody.bind, resolve]) messageBound hm hl hg behavior

end

def failureMessage (access : Bool) : String :=
  if access then accessMessage else ErrorCalls.rejectionMessage

def FailureCondition (access : Bool) (kind : Kind) (mode : Mode) (buffer : Option Address) (count : UInt64) : Prop :=
  if access then Reference.Allowed .getNominals kind mode ∧ (count.toNat ≠ 1 ∨ buffer = none)
  else ¬ Reference.Allowed .getNominals kind mode

theorem failure_message_collected (model : Solve.FMI3Model source) (access : Bool) :
    failureMessage access ∈ functionTexts (Runtime.function model ErrorCalls.nominalSignature) := by
  cases access <;>
    simp [failureMessage, accessMessage, Runtime.function, Runtime.body,
      ErrorCalls.nominalSignature, ErrorCalls.rejectionMessage, Runtime.require,
      Runtime.instancePrefix, Runtime.modeGuard, Runtime.branch, Runtime.fail,
      Runtime.ret, Runtime.call, Runtime.v, Runtime.scalarAccessCheck, Runtime.reject,
      functionTexts, statementTexts, expressionTexts]

section
variable [static : StaticLiterals]
private local instance failureInterface : CInterface := cInterface static.addresses

theorem failure_all_behaviors (model : Solve.FMI3Model source) (access : Bool)
    (program : CCalls.Events.Program E) (heap : Heap)
    (p message category logger : Address) (environment buffer : Option Address)
    (count : UInt64) (kind : Kind) (mode : Mode) (name : String) (foreign : CCalls.Events.External E)
    (defined : program.internal.definitions ErrorCalls.nominalSignature.name =
      some (.tree (Runtime.function model ErrorCalls.nominalSignature)))
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (messageBound : static.addresses (failureMessage access) = some message)
    (address : program.addresses logger = some name)
    (external : program.externals name = some foreign)
    (prototype : foreign.signature = Logging.signature name)
    (literal : static.addresses "logStatus" = some category)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (hl : load heap (p.member "logger") = some (.pointer (some logger)))
    (hg : load heap (p.member "logging") = some (.integer 1))
    (he : load heap (p.member "environment") = some (.pointer environment))
    (condition : FailureCondition access kind mode buffer count) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling ErrorCalls.nominalSignature.name (ErrorCalls.nominalArguments p buffer count) heap .done) behavior ↔
      (∃ events value after, foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) events value after ∧
        behavior = .terminates events ⟨.integer 3, after⟩) ∨
      ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) events value after) ∧ behavior = .wrong []) := by
  cases access with
  | false =>
      exact reject_all_behaviors model program heap p message category logger
        environment buffer count kind mode name foreign defined helper messageBound address external prototype
        literal hk hm hl hg he condition behavior
  | true =>
      exact invalid_all_behaviors model program heap p message category logger
        environment buffer count kind mode name foreign defined helper messageBound address external prototype
        literal hk hm hl hg he condition.1 condition.2 behavior

theorem failure_silent_behaviors (model : Solve.FMI3Model source) (access : Bool)
    (program : CCalls.Events.Program E) (heap : Heap) (p message : Address)
    (buffer logger : Option Address) (count : UInt64) (kind : Kind) (mode : Mode)
    (defined : program.internal.definitions ErrorCalls.nominalSignature.name =
      some (.tree (Runtime.function model ErrorCalls.nominalSignature)))
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (messageBound : static.addresses (failureMessage access) = some message)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (hl : load heap (p.member "logger") = some (.pointer logger))
    (hg : load heap (p.member "logging") = some (.integer 0))
    (condition : FailureCondition access kind mode buffer count) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling ErrorCalls.nominalSignature.name (ErrorCalls.nominalArguments p buffer count) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩ := by
  cases access with
  | false =>
      exact reject_silent_behaviors model program heap p message buffer logger
        count kind mode defined helper messageBound hk hm hl hg condition behavior
  | true =>
      exact invalid_silent_behaviors model program heap p message buffer logger
        count kind mode defined helper messageBound hk hm hl hg condition.1 condition.2 behavior

end

/-- Exhaustive classification of argument/lifecycle cases. Memory validity and
admissible host bindings remain explicit premises of the corresponding contract. -/
theorem query_cases (kind : Kind) (mode : Mode) (handle buffer : Option Address) (count : UInt64) :
    handle = none ∨ ∃ p, handle = some p ∧
      ((∃ output, buffer = some output ∧ count = 1 ∧ Reference.Allowed .getNominals kind mode) ∨
       FailureCondition false kind mode buffer count ∨ FailureCondition true kind mode buffer count) := by
  classical
  cases handle with
  | none => exact Or.inl rfl
  | some p =>
      refine Or.inr ⟨p, rfl, ?_⟩
      by_cases allowed : Reference.Allowed .getNominals kind mode
      · by_cases size : count.toNat = 1
        · cases buffer with
          | none => exact Or.inr (Or.inr ⟨allowed, Or.inr rfl⟩)
          | some output =>
              have countOne : count = 1 := UInt64.toNat_inj.mp size
              exact Or.inl ⟨output, rfl, countOne, allowed⟩
        · exact Or.inr (Or.inr ⟨allowed, Or.inl size⟩)
      · exact Or.inr (Or.inl allowed)

theorem failure_cases_disjoint
    (lifecycle : FailureCondition false kind mode buffer count)
    (access : FailureCondition true kind mode buffer count) : False := lifecycle access.1

end Rumoca.FMI3.Nominals
