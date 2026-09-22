import RumocaFMI3.PreparedStepLiterals

/-! Whole rejected public calls with diagnostics derived from the actual
prepared pool and contents preserved up to callback entry, not after it.
Installation freshness, external interpretation and native realization remain
explicit. The same function table supplies every definition used below. -/

noncomputable section
namespace Rumoca.FMI3.PreparedLifecycleFailureCall
open CTree CMemory CLiteral
open CLiteral (StoredContents)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- Lifecycle rejection in the actual prepared tensor adapter. The
diagnostic and category have derived C-string storage at callback entry; the
callback's own heap effects remain arbitrary. -/
theorem tensor_logged_for {source : AST.Model} {shape : Tensor.Shape} {E : Type}
    (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape) (sigs : List Signature)
    (stepMember : StepEntry.signature ∈ sigs)
    (target : CCalls.Program)
    (stepDefinition : target.definitions "fmi3DoStep" = some (.tree (TensorDoStep.function shape m.hasOutput)))
    (failureDefinition : target.definitions "fail" = some (.tree Runtime.helpers[0]))
    {pool : Pool (LiteralPreparation.excluded ++
      (TensorFunctions.functions model m sigs).flatMap functionNames)}
    (made : TensorFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (outputs : StepEntry.Outputs) (point step : BitVec 64) (flag : Bool)
      (kind : Kind) (mode : Mode)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = target →
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    ¬ Reference.Allowed .doStep kind mode →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock ErrorCalls.rejectionMessage = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode heap p .terminated) message ErrorCalls.rejectionMessage ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode heap p .terminated) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point step flag outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode heap p .terminated) events value after ∧
          behavior = .terminates events ⟨.integer 3, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode heap p .terminated) events value after) ∧ behavior = .wrong []) := by
  letI : CInterface := context.target
  intro program p logger outputs point step flag kind mode environment name foreign linked kindValue modeCell
    rejected loggerValue loggingValue environmentValue address external prototype
  have callbackFrame := frame.trans
    (LifecycleBodies.writeMode_readonly heap p .terminated (some (.integer mode.code)) modeCell)
  obtain ⟨message, category, messageBound, categoryBound, messageStored, categoryStored⟩ :=
    PreparedLifecycleLiterals.tensor_prepared model m sigs stepMember made before firstBlock signed
      (LifecycleBodies.writeMode heap p .terminated) callbackFrame
  have defined : program.internal.definitions "fmi3DoStep" =
      some (.tree (TensorDoStep.function shape m.hasOutput)) := by
    rw [linked]
    exact stepDefinition
  have helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) := by
    rw [linked]
    exact failureDefinition
  refine ⟨message, category, messageBound, categoryBound, messageStored, categoryStored, ?_⟩
  have modeValue : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, modeCell, convert, Mode.code]
  have certified := StepErrors.lifecycle_prefix_for_tail context (TensorDoStep.function shape m.hasOutput)
    (StepEntry.outputCode ++ StepEntry.inputGuard ::
      (Runtime.stepRounding ++ Runtime.stepClock ++ Runtime.stepGrid ++ TensorDoStep.tensorStepSolve shape m.hasOutput))
    rfl (by simp [TensorDoStep.function, TensorDoStep.doStepBody, StepEntry.outputCode,
      StepEntry.inputGuard, StepEntry.inputCondition, List.append_assoc]) (TensorDoStep.doStepBody_closed shape m.hasOutput)
    heap p point step flag outputs kind mode kindValue modeValue rejected
  exact StaticErrors.prefix_all_behaviors context program (TensorDoStep.function shape m.hasOutput)
    (StepEntry.arguments (some p) point step flag outputs) heap heap p message category logger
    ErrorCalls.rejectionMessage name environment (some (.integer mode.code)) foreign certified defined helper
    messageBound address external prototype categoryBound modeCell loggerValue loggingValue environmentValue

theorem tensor_logged {source : AST.Model} {shape : Tensor.Shape} {E : Type}
    (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape) (sigs : List Signature)
    (stepMember : StepEntry.signature ∈ sigs)
    (unique : ((TensorFunctions.functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    {pool : Pool (LiteralPreparation.excluded ++
      (TensorFunctions.functions model m sigs).flatMap functionNames)}
    (made : TensorFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (outputs : StepEntry.Outputs) (point step : BitVec 64) (flag : Bool)
      (kind : Kind) (mode : Mode)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = TensorFunctions.program model m sigs →
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    ¬ Reference.Allowed .doStep kind mode →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock ErrorCalls.rejectionMessage = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode heap p .terminated) message ErrorCalls.rejectionMessage ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode heap p .terminated) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point step flag outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode heap p .terminated) events value after ∧
          behavior = .terminates events ⟨.integer 3, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode heap p .terminated) events value after) ∧ behavior = .wrong []) := by
  exact tensor_logged_for model m sigs stepMember (TensorFunctions.program model m sigs)
    (TensorFunctions.doStep_bound model m sigs unique stepMember)
    (TensorFunctions.helpers_bound model m sigs Runtime.helpers[0] (by simp [TensorFunctions.helpers]))
    made before firstBlock signed heap frame context

/-- The corresponding whole-call result for every prepared constant-rate
adapter, with addresses and callback-entry contents from that same pool. -/
theorem constant_logged {source : AST.Model} {n : Nat} {E : Type}
    (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n) (sigs : List Signature)
    (stepMember : StepEntry.signature ∈ sigs)
    (unique : ((ConstantFunctions.functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    {pool : Pool (LiteralPreparation.excluded ++
      (ConstantFunctions.functions model m sigs).flatMap functionNames)}
    (made : ConstantFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (outputs : StepEntry.Outputs) (point step : BitVec 64) (flag : Bool)
      (kind : Kind) (mode : Mode)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = ConstantFunctions.program model m sigs →
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    ¬ Reference.Allowed .doStep kind mode →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock ErrorCalls.rejectionMessage = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode heap p .terminated) message ErrorCalls.rejectionMessage ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode heap p .terminated) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point step flag outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode heap p .terminated) events value after ∧
          behavior = .terminates events ⟨.integer 3, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode heap p .terminated) events value after) ∧ behavior = .wrong []) := by
  letI : CInterface := context.target
  intro program p logger outputs point step flag kind mode environment name foreign linked kindValue modeCell
    rejected loggerValue loggingValue environmentValue address external prototype
  have callbackFrame := frame.trans
    (LifecycleBodies.writeMode_readonly heap p .terminated (some (.integer mode.code)) modeCell)
  obtain ⟨message, category, messageBound, categoryBound, messageStored, categoryStored⟩ :=
    PreparedLifecycleLiterals.constant_prepared model m sigs stepMember made before firstBlock signed
      (LifecycleBodies.writeMode heap p .terminated) callbackFrame
  have defined : program.internal.definitions "fmi3DoStep" = some (.tree ConstantDoStep.function) := by
    rw [linked]
    exact ConstantFunctions.doStep_bound model m sigs unique stepMember
  have helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) := by
    rw [linked]
    exact ConstantFunctions.helpers_bound model m sigs Runtime.helpers[0]
      (by simp [ConstantFunctions.helpers, TensorFunctions.helpers])
  refine ⟨message, category, messageBound, categoryBound, messageStored, categoryStored, ?_⟩
  have modeValue : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, modeCell, convert, Mode.code]
  have certified := StepErrors.lifecycle_prefix_for_tail context ConstantDoStep.function
    (StepEntry.outputCode ++ StepEntry.inputGuard ::
      (Runtime.stepRounding ++ Runtime.stepClock ++ Runtime.stepGrid ++ ConstantDoStep.stepSolve))
    rfl (by simp [ConstantDoStep.function, ConstantDoStep.doStepBody, StepEntry.outputCode,
      StepEntry.inputGuard, StepEntry.inputCondition, List.append_assoc]) ConstantDoStep.doStepBody_closed
    heap p point step flag outputs kind mode kindValue modeValue rejected
  exact StaticErrors.prefix_all_behaviors context program ConstantDoStep.function
    (StepEntry.arguments (some p) point step flag outputs) heap heap p message category logger
    ErrorCalls.rejectionMessage name environment (some (.integer mode.code)) foreign certified defined helper
    messageBound address external prototype categoryBound modeCell loggerValue loggingValue environmentValue

end Rumoca.FMI3.PreparedLifecycleFailureCall

noncomputable section
namespace Rumoca.FMI3.PreparedOutputFailureCall
open CTree CMemory CLiteral
open CLiteral (StoredContents)

/-- Missing-output rejection in the actual prepared tensor adapter. The
diagnostic and category have derived C-string storage at callback entry; the
callback's own heap effects remain arbitrary. -/
theorem tensor_logged_for {source : AST.Model} {shape : Tensor.Shape} {E : Type}
    (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape) (sigs : List Signature)
    (stepMember : StepEntry.signature ∈ sigs)
    (target : CCalls.Program)
    (stepDefinition : target.definitions "fmi3DoStep" = some (.tree (TensorDoStep.function shape m.hasOutput)))
    (failureDefinition : target.definitions "fail" = some (.tree Runtime.helpers[0]))
    {pool : Pool (LiteralPreparation.excluded ++
      (TensorFunctions.functions model m sigs).flatMap functionNames)}
    (made : TensorFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (outputs : StepEntry.Outputs) (point step : BitVec 64) (flag : Bool)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = target →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    StepArguments.MissingOutput outputs →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock "Missing output pointer" = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode heap p .terminated) message "Missing output pointer" ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode heap p .terminated) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point step flag outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode heap p .terminated) events value after ∧
          behavior = .terminates events ⟨.integer 3, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode heap p .terminated) events value after) ∧ behavior = .wrong []) := by
  letI : CInterface := context.target
  intro program p logger outputs point step flag environment name foreign linked kindValue modeCell
    missing loggerValue loggingValue environmentValue address external prototype
  have callbackFrame := frame.trans
    (LifecycleBodies.writeMode_readonly heap p .terminated (some (.integer 4)) modeCell)
  obtain ⟨message, category, messageBound, categoryBound, messageStored, categoryStored⟩ :=
    PreparedArgumentLiterals.tensor_prepared model m sigs stepMember made before firstBlock signed
      (LifecycleBodies.writeMode heap p .terminated) callbackFrame "Missing output pointer" (Or.inl rfl)
  have defined : program.internal.definitions "fmi3DoStep" =
      some (.tree (TensorDoStep.function shape m.hasOutput)) := by
    rw [linked]
    exact stepDefinition
  have helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) := by
    rw [linked]
    exact failureDefinition
  refine ⟨message, category, messageBound, categoryBound, messageStored, categoryStored, ?_⟩
  exact (TensorDoStep.output_rejection_contract shape m.hasOutput).logged
    (pool.addresses firstBlock) context program heap p message category logger outputs point step flag
    environment name foreign defined helper messageBound address external prototype categoryBound
    kindValue modeCell loggerValue loggingValue environmentValue missing

theorem tensor_logged {source : AST.Model} {shape : Tensor.Shape} {E : Type}
    (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape) (sigs : List Signature)
    (stepMember : StepEntry.signature ∈ sigs)
    (unique : ((TensorFunctions.functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    {pool : Pool (LiteralPreparation.excluded ++
      (TensorFunctions.functions model m sigs).flatMap functionNames)}
    (made : TensorFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (outputs : StepEntry.Outputs) (point step : BitVec 64) (flag : Bool)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = TensorFunctions.program model m sigs →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    StepArguments.MissingOutput outputs →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock "Missing output pointer" = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode heap p .terminated) message "Missing output pointer" ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode heap p .terminated) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point step flag outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode heap p .terminated) events value after ∧
          behavior = .terminates events ⟨.integer 3, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode heap p .terminated) events value after) ∧ behavior = .wrong []) := by
  exact tensor_logged_for model m sigs stepMember (TensorFunctions.program model m sigs)
    (TensorFunctions.doStep_bound model m sigs unique stepMember)
    (TensorFunctions.helpers_bound model m sigs Runtime.helpers[0] (by simp [TensorFunctions.helpers]))
    made before firstBlock signed heap frame context

/-- The corresponding whole-call result for every prepared constant-rate
adapter, with addresses and callback-entry contents from that same pool. -/
theorem constant_logged {source : AST.Model} {n : Nat} {E : Type}
    (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n) (sigs : List Signature)
    (stepMember : StepEntry.signature ∈ sigs)
    (unique : ((ConstantFunctions.functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    {pool : Pool (LiteralPreparation.excluded ++
      (ConstantFunctions.functions model m sigs).flatMap functionNames)}
    (made : ConstantFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (outputs : StepEntry.Outputs) (point step : BitVec 64) (flag : Bool)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = ConstantFunctions.program model m sigs →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    StepArguments.MissingOutput outputs →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock "Missing output pointer" = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode heap p .terminated) message "Missing output pointer" ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode heap p .terminated) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point step flag outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode heap p .terminated) events value after ∧
          behavior = .terminates events ⟨.integer 3, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode heap p .terminated) events value after) ∧ behavior = .wrong []) := by
  letI : CInterface := context.target
  intro program p logger outputs point step flag environment name foreign linked kindValue modeCell
    missing loggerValue loggingValue environmentValue address external prototype
  have callbackFrame := frame.trans
    (LifecycleBodies.writeMode_readonly heap p .terminated (some (.integer 4)) modeCell)
  obtain ⟨message, category, messageBound, categoryBound, messageStored, categoryStored⟩ :=
    PreparedArgumentLiterals.constant_prepared model m sigs stepMember made before firstBlock signed
      (LifecycleBodies.writeMode heap p .terminated) callbackFrame "Missing output pointer" (Or.inl rfl)
  have defined : program.internal.definitions "fmi3DoStep" = some (.tree ConstantDoStep.function) := by
    rw [linked]
    exact ConstantFunctions.doStep_bound model m sigs unique stepMember
  have helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) := by
    rw [linked]
    exact ConstantFunctions.helpers_bound model m sigs Runtime.helpers[0]
      (by simp [ConstantFunctions.helpers, TensorFunctions.helpers])
  refine ⟨message, category, messageBound, categoryBound, messageStored, categoryStored, ?_⟩
  exact ConstantDoStep.output_rejection_contract.logged
    (pool.addresses firstBlock) context program heap p message category logger outputs point step flag
    environment name foreign defined helper messageBound address external prototype categoryBound
    kindValue modeCell loggerValue loggingValue environmentValue missing

end Rumoca.FMI3.PreparedOutputFailureCall

noncomputable section
namespace Rumoca.FMI3.PreparedInputFailureCall
open CTree CMemory CLiteral
open CLiteral (StoredContents)

/-- Invalid-input rejection in the actual prepared tensor adapter. Output
initialization and the mode write preserve the pool's diagnostic and category
storage at callback entry; the callback's own heap effects remain arbitrary. -/
theorem tensor_logged_for {source : AST.Model} {shape : Tensor.Shape} {E : Type}
    (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape) (sigs : List Signature)
    (stepMember : StepEntry.signature ∈ sigs)
    (target : CCalls.Program)
    (stepDefinition : target.definitions "fmi3DoStep" = some (.tree (TensorDoStep.function shape m.hasOutput)))
    (failureDefinition : target.definitions "fail" = some (.tree Runtime.helpers[0]))
    {pool : Pool (LiteralPreparation.excluded ++
      (TensorFunctions.functions model m sigs).flatMap functionNames)}
    (made : TensorFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (buffers : StepEntry.Buffers) (point step : BitVec 64) (time : Binary64.Value) (flag : Bool)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = target →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    load heap (p.member "time") = some (.finite time) →
    StepArguments.Storage heap p buffers → ¬ StepEntry.InputsValid point step time →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock StepArguments.inputMessage = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) message StepArguments.inputMessage ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point step flag buffers.outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after ∧
          behavior = .terminates events ⟨.integer 3, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after) ∧ behavior = .wrong []) := by
  letI : CInterface := context.target
  intro program p logger buffers point step time flag environment name foreign linked kindValue modeCell
    clock stored invalid loggerValue loggingValue environmentValue address external prototype
  have callbackFrame := frame.trans
    (stored.error_readonly time (some (.integer 4)) modeCell)
  obtain ⟨message, category, messageBound, categoryBound, messageStored, categoryStored⟩ :=
    PreparedArgumentLiterals.tensor_prepared model m sigs stepMember made before firstBlock signed
      (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) callbackFrame StepArguments.inputMessage (Or.inr rfl)
  have defined : program.internal.definitions "fmi3DoStep" =
      some (.tree (TensorDoStep.function shape m.hasOutput)) := by
    rw [linked]
    exact stepDefinition
  have helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) := by
    rw [linked]
    exact failureDefinition
  refine ⟨message, category, messageBound, categoryBound, messageStored, categoryStored, ?_⟩
  exact (TensorDoStep.input_rejection_contract shape m.hasOutput).logged
    (pool.addresses firstBlock) context program heap p message category logger buffers point step time flag
    environment name foreign defined helper messageBound address external prototype categoryBound
    kindValue modeCell clock stored loggerValue loggingValue environmentValue invalid

theorem tensor_logged {source : AST.Model} {shape : Tensor.Shape} {E : Type}
    (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape) (sigs : List Signature)
    (stepMember : StepEntry.signature ∈ sigs)
    (unique : ((TensorFunctions.functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    {pool : Pool (LiteralPreparation.excluded ++
      (TensorFunctions.functions model m sigs).flatMap functionNames)}
    (made : TensorFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (buffers : StepEntry.Buffers) (point step : BitVec 64) (time : Binary64.Value) (flag : Bool)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = TensorFunctions.program model m sigs →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    load heap (p.member "time") = some (.finite time) →
    StepArguments.Storage heap p buffers → ¬ StepEntry.InputsValid point step time →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock StepArguments.inputMessage = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) message StepArguments.inputMessage ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point step flag buffers.outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after ∧
          behavior = .terminates events ⟨.integer 3, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after) ∧ behavior = .wrong []) := by
  exact tensor_logged_for model m sigs stepMember (TensorFunctions.program model m sigs)
    (TensorFunctions.doStep_bound model m sigs unique stepMember)
    (TensorFunctions.helpers_bound model m sigs Runtime.helpers[0] (by simp [TensorFunctions.helpers]))
    made before firstBlock signed heap frame context

/-- The corresponding whole-call result for every prepared constant-rate
adapter, with addresses and callback-entry contents from that same pool. -/
theorem constant_logged {source : AST.Model} {n : Nat} {E : Type}
    (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n) (sigs : List Signature)
    (stepMember : StepEntry.signature ∈ sigs)
    (unique : ((ConstantFunctions.functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    {pool : Pool (LiteralPreparation.excluded ++
      (ConstantFunctions.functions model m sigs).flatMap functionNames)}
    (made : ConstantFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (buffers : StepEntry.Buffers) (point step : BitVec 64) (time : Binary64.Value) (flag : Bool)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = ConstantFunctions.program model m sigs →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    load heap (p.member "time") = some (.finite time) →
    StepArguments.Storage heap p buffers → ¬ StepEntry.InputsValid point step time →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock StepArguments.inputMessage = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) message StepArguments.inputMessage ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point step flag buffers.outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after ∧
          behavior = .terminates events ⟨.integer 3, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after) ∧ behavior = .wrong []) := by
  letI : CInterface := context.target
  intro program p logger buffers point step time flag environment name foreign linked kindValue modeCell
    clock stored invalid loggerValue loggingValue environmentValue address external prototype
  have callbackFrame := frame.trans
    (stored.error_readonly time (some (.integer 4)) modeCell)
  obtain ⟨message, category, messageBound, categoryBound, messageStored, categoryStored⟩ :=
    PreparedArgumentLiterals.constant_prepared model m sigs stepMember made before firstBlock signed
      (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) callbackFrame StepArguments.inputMessage (Or.inr rfl)
  have defined : program.internal.definitions "fmi3DoStep" = some (.tree ConstantDoStep.function) := by
    rw [linked]
    exact ConstantFunctions.doStep_bound model m sigs unique stepMember
  have helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) := by
    rw [linked]
    exact ConstantFunctions.helpers_bound model m sigs Runtime.helpers[0]
      (by simp [ConstantFunctions.helpers, TensorFunctions.helpers])
  refine ⟨message, category, messageBound, categoryBound, messageStored, categoryStored, ?_⟩
  exact ConstantDoStep.input_rejection_contract.logged
    (pool.addresses firstBlock) context program heap p message category logger buffers point step time flag
    environment name foreign defined helper messageBound address external prototype categoryBound
    kindValue modeCell clock stored loggerValue loggingValue environmentValue invalid

end Rumoca.FMI3.PreparedInputFailureCall

noncomputable section
namespace Rumoca.FMI3.PreparedNumericFailureCall
open CTree CMemory CLiteral CBody
open CLiteral (StoredContents)
set_option autoImplicit false

/-- Prepared tensor rounding rejection: derive diagnostic/category addresses and
contents at callback entry, and retain every represented callback outcome.
Outputs are initialized before the terminated-mode write; neither write destroys literals.
No post-callback storage frame or native correspondence is claimed. -/
theorem tensor_rounding_logged_for {source : AST.Model} {shape : Tensor.Shape} {E : Type}
    (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape) (sigs : List Signature)
    (stepMember : StepEntry.signature ∈ sigs)
    (target : CCalls.Program)
    (stepDefinition : target.definitions "fmi3DoStep" = some (.tree (TensorDoStep.function shape m.hasOutput)))
    (failureDefinition : target.definitions "fail" = some (.tree Runtime.helpers[0]))
    {pool : Pool (LiteralPreparation.excluded ++
      (TensorFunctions.functions model m sigs).flatMap functionNames)}
    (made : TensorFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)) (header : CFenv.Header) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (buffers : StepEntry.Buffers) (point step : BitVec 64) (time : Binary64.Value)
      (flag : Bool) (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
      (integer : context.target.types "int" = some .int32)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = target →
    context.target.constants "fegetround" = none →
    context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
    program.externals "fegetround" = some (CMathCalls.roundingExternal integer observed range) →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    load heap (p.member "time") = some (.finite time) →
    StepArguments.Storage heap p buffers → StepEntry.InputsValid point step time →
    observed ≠ header.nearest →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock StepFailures.roundingMessage = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) message StepFailures.roundingMessage ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point step flag buffers.outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after ∧
          behavior = .terminates events ⟨.integer 3, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after) ∧ behavior = .wrong []) := by
  letI : CInterface := context.target
  intro program p logger buffers point step time flag observed range integer environment name foreign linked
    ordinary macroBound rounding kindValue modeCell clock stored valid
    rejected loggerValue loggingValue environmentValue address external prototype
  have callbackFrame := frame.trans (stored.error_readonly time (some (.integer 4)) modeCell)
  obtain ⟨message, category, messageBound, categoryBound, messageStored, categoryStored⟩ :=
    PreparedNumericLiterals.tensor_prepared model m sigs stepMember made before firstBlock signed
      (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) callbackFrame StepFailures.roundingMessage (Or.inl rfl)
  have defined : program.internal.definitions "fmi3DoStep" = some (.tree (TensorDoStep.function shape m.hasOutput)) := by
    rw [linked]
    exact stepDefinition
  have helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) := by
    rw [linked]
    exact failureDefinition
  refine ⟨message, category, messageBound, categoryBound, messageStored, categoryStored, ?_⟩
  exact (TensorDoStep.rounding_rejection_contract shape m.hasOutput).logged
    (pool.addresses firstBlock) context header program heap p message category logger buffers point step time flag
    observed range integer environment name foreign ordinary macroBound rounding defined helper messageBound
    address external prototype categoryBound kindValue modeCell clock stored valid rejected
    loggerValue loggingValue environmentValue

theorem tensor_rounding_logged {source : AST.Model} {shape : Tensor.Shape} {E : Type}
    (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape) (sigs : List Signature)
    (stepMember : StepEntry.signature ∈ sigs)
    (unique : ((TensorFunctions.functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    {pool : Pool (LiteralPreparation.excluded ++
      (TensorFunctions.functions model m sigs).flatMap functionNames)}
    (made : TensorFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)) (header : CFenv.Header) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (buffers : StepEntry.Buffers) (point step : BitVec 64) (time : Binary64.Value)
      (flag : Bool) (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
      (integer : context.target.types "int" = some .int32)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = TensorFunctions.program model m sigs →
    context.target.constants "fegetround" = none →
    context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
    program.externals "fegetround" = some (CMathCalls.roundingExternal integer observed range) →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    load heap (p.member "time") = some (.finite time) →
    StepArguments.Storage heap p buffers → StepEntry.InputsValid point step time →
    observed ≠ header.nearest →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock StepFailures.roundingMessage = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) message StepFailures.roundingMessage ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point step flag buffers.outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after ∧
          behavior = .terminates events ⟨.integer 3, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after) ∧ behavior = .wrong []) := by
  exact tensor_rounding_logged_for model m sigs stepMember (TensorFunctions.program model m sigs)
    (TensorFunctions.doStep_bound model m sigs unique stepMember)
    (TensorFunctions.helpers_bound model m sigs Runtime.helpers[0] (by simp [TensorFunctions.helpers]))
    made before firstBlock signed heap frame context header

/-- Prepared tensor stop rejection: derive diagnostic/category addresses and
contents at callback entry, and retain every represented callback outcome.
Outputs are initialized before the terminated-mode write; neither write destroys literals.
No post-callback storage frame or native correspondence is claimed. -/
theorem tensor_stop_logged_for {source : AST.Model} {shape : Tensor.Shape} {E : Type}
    (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape) (sigs : List Signature)
    (stepMember : StepEntry.signature ∈ sigs)
    (target : CCalls.Program)
    (stepDefinition : target.definitions "fmi3DoStep" = some (.tree (TensorDoStep.function shape m.hasOutput)))
    (failureDefinition : target.definitions "fail" = some (.tree Runtime.helpers[0]))
    {pool : Pool (LiteralPreparation.excluded ++
      (TensorFunctions.functions model m sigs).flatMap functionNames)}
    (made : TensorFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)) (header : CFenv.Header) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (buffers : StepEntry.Buffers) (point : BitVec 64) (step time : Binary64.Value)
      (flag : Bool) (stop : Option Binary64.Value)
      (integer : context.target.types "int" = some .int32)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = target →
    context.target.constants "fegetround" = none →
    context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
    program.externals "fegetround" = some (CMathCalls.roundingExternal integer header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    load heap (p.member "time") = some (.finite time) →
    StepArguments.Storage heap p buffers → StepEntry.InputsValid point (Binary64.toBits step).val time →
    load heap (p.member "stopDefined") = some (boolean stop.isSome) →
    (∀ value, stop = some value → load heap (p.member "stop") = some (.finite value)) →
    StepGuards.AboveStop (Binary64.addResult time step) stop →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock StepFailures.stopMessage = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) message StepFailures.stopMessage ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point (Binary64.toBits step).val flag buffers.outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after ∧
          behavior = .terminates events ⟨.integer 3, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after) ∧ behavior = .wrong []) := by
  letI : CInterface := context.target
  intro program p logger buffers point step time flag stop integer environment name foreign linked
    ordinary macroBound rounding kindValue modeCell clock stored valid
    enabled limit rejected loggerValue loggingValue environmentValue address external prototype
  have callbackFrame := frame.trans (stored.error_readonly time (some (.integer 4)) modeCell)
  obtain ⟨message, category, messageBound, categoryBound, messageStored, categoryStored⟩ :=
    PreparedNumericLiterals.tensor_prepared model m sigs stepMember made before firstBlock signed
      (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) callbackFrame StepFailures.stopMessage (Or.inr (Or.inl rfl))
  have defined : program.internal.definitions "fmi3DoStep" = some (.tree (TensorDoStep.function shape m.hasOutput)) := by
    rw [linked]
    exact stepDefinition
  have helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) := by
    rw [linked]
    exact failureDefinition
  refine ⟨message, category, messageBound, categoryBound, messageStored, categoryStored, ?_⟩
  exact (TensorDoStep.stop_rejection_contract shape m.hasOutput).logged
    (pool.addresses firstBlock) context header program heap p message category logger buffers point step time flag
    stop integer environment name foreign ordinary macroBound rounding defined helper messageBound categoryBound
    address external prototype kindValue modeCell clock stored valid enabled limit rejected
    loggerValue loggingValue environmentValue

theorem tensor_stop_logged {source : AST.Model} {shape : Tensor.Shape} {E : Type}
    (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape) (sigs : List Signature)
    (stepMember : StepEntry.signature ∈ sigs)
    (unique : ((TensorFunctions.functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    {pool : Pool (LiteralPreparation.excluded ++
      (TensorFunctions.functions model m sigs).flatMap functionNames)}
    (made : TensorFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)) (header : CFenv.Header) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (buffers : StepEntry.Buffers) (point : BitVec 64) (step time : Binary64.Value)
      (flag : Bool) (stop : Option Binary64.Value)
      (integer : context.target.types "int" = some .int32)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = TensorFunctions.program model m sigs →
    context.target.constants "fegetround" = none →
    context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
    program.externals "fegetround" = some (CMathCalls.roundingExternal integer header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    load heap (p.member "time") = some (.finite time) →
    StepArguments.Storage heap p buffers → StepEntry.InputsValid point (Binary64.toBits step).val time →
    load heap (p.member "stopDefined") = some (boolean stop.isSome) →
    (∀ value, stop = some value → load heap (p.member "stop") = some (.finite value)) →
    StepGuards.AboveStop (Binary64.addResult time step) stop →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock StepFailures.stopMessage = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) message StepFailures.stopMessage ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point (Binary64.toBits step).val flag buffers.outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after ∧
          behavior = .terminates events ⟨.integer 3, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after) ∧ behavior = .wrong []) := by
  exact tensor_stop_logged_for model m sigs stepMember (TensorFunctions.program model m sigs)
    (TensorFunctions.doStep_bound model m sigs unique stepMember)
    (TensorFunctions.helpers_bound model m sigs Runtime.helpers[0] (by simp [TensorFunctions.helpers]))
    made before firstBlock signed heap frame context header

/-- Prepared tensor discard rejection: derive diagnostic/category addresses and
contents at callback entry, and retain every represented callback outcome.
No mode write, writable-mode premise, or failure-helper binding is required.
No post-callback storage frame or native correspondence is claimed. -/
theorem tensor_discard_logged_for {source : AST.Model} {shape : Tensor.Shape} {E : Type}
    (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape) (sigs : List Signature)
    (stepMember : StepEntry.signature ∈ sigs)
    (target : CCalls.Program)
    (stepDefinition : target.definitions "fmi3DoStep" = some (.tree (TensorDoStep.function shape m.hasOutput)))
    {pool : Pool (LiteralPreparation.excluded ++
      (TensorFunctions.functions model m sigs).flatMap functionNames)}
    (made : TensorFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)) (header : CFenv.Header) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (buffers : StepEntry.Buffers) (point : BitVec 64) (step time : Binary64.Value)
      (flag : Bool) (stop : Option Binary64.Value)
      (integer : context.target.types "int" = some .int32)
      (double : context.target.types "double" = some .float64)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = target →
    context.target.constants "fegetround" = none →
    context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
    context.target.constants "fmi3Discard" = some (.integer 2) →
    program.externals "fegetround" = some (CMathCalls.roundingExternal integer header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
    (StepGuards.Progress time (Binary64.addResult time step) →
      context.target.constants "floor" = none ∧
      program.externals "floor" = some (CMathCalls.floorExternal double)) →
    load heap (p.member "kind") = some (.integer 1) →
    load heap (p.member "mode") = some (.integer 4) →
    load heap (p.member "time") = some (.finite time) →
    StepArguments.Storage heap p buffers → StepEntry.InputsValid point (Binary64.toBits step).val time →
    load heap (p.member "stopDefined") = some (boolean stop.isSome) →
    (∀ value, stop = some value → load heap (p.member "stop") = some (.finite value)) →
    ¬ StepGuards.AboveStop (Binary64.addResult time step) stop →
    StepDiscard.Rejected time step →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock StepDiscard.message = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (StepEntry.outputHeap heap buffers time) message StepDiscard.message ∧
      StoredContents signed (pool.install before firstBlock signed)
        (StepEntry.outputHeap heap buffers time) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point (Binary64.toBits step).val flag buffers.outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (StepDiscard.arguments environment category message)
          (StepEntry.outputHeap heap buffers time) events value after ∧
          behavior = .terminates events ⟨.integer 2, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (StepDiscard.arguments environment category message)
          (StepEntry.outputHeap heap buffers time) events value after) ∧ behavior = .wrong []) := by
  letI : CInterface := context.target
  intro program p logger buffers point step time flag stop integer double environment name foreign linked
    ordinary macroBound discardBound rounding floorBound kindValue modeCell clock stored valid
    enabled limit noStop rejected loggerValue loggingValue environmentValue address external prototype
  have callbackFrame := frame.trans (stored.output_readonly time)
  obtain ⟨message, category, messageBound, categoryBound, messageStored, categoryStored⟩ :=
    PreparedNumericLiterals.tensor_prepared model m sigs stepMember made before firstBlock signed
      (StepEntry.outputHeap heap buffers time) callbackFrame StepDiscard.message (Or.inr (Or.inr rfl))
  have defined : program.internal.definitions "fmi3DoStep" = some (.tree (TensorDoStep.function shape m.hasOutput)) := by
    rw [linked]
    exact stepDefinition
  refine ⟨message, category, messageBound, categoryBound, messageStored, categoryStored, ?_⟩
  exact (TensorDoStep.discard_rejection_contract shape m.hasOutput).logged
    (pool.addresses firstBlock) context header program heap p message category logger buffers point step time flag
    stop integer double environment name foreign ordinary macroBound discardBound rounding floorBound defined
    kindValue modeCell clock stored valid enabled limit noStop rejected categoryBound messageBound
    address external prototype loggerValue loggingValue environmentValue

theorem tensor_discard_logged {source : AST.Model} {shape : Tensor.Shape} {E : Type}
    (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape) (sigs : List Signature)
    (stepMember : StepEntry.signature ∈ sigs)
    (unique : ((TensorFunctions.functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    {pool : Pool (LiteralPreparation.excluded ++
      (TensorFunctions.functions model m sigs).flatMap functionNames)}
    (made : TensorFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)) (header : CFenv.Header) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (buffers : StepEntry.Buffers) (point : BitVec 64) (step time : Binary64.Value)
      (flag : Bool) (stop : Option Binary64.Value)
      (integer : context.target.types "int" = some .int32)
      (double : context.target.types "double" = some .float64)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = TensorFunctions.program model m sigs →
    context.target.constants "fegetround" = none →
    context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
    context.target.constants "fmi3Discard" = some (.integer 2) →
    program.externals "fegetround" = some (CMathCalls.roundingExternal integer header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
    (StepGuards.Progress time (Binary64.addResult time step) →
      context.target.constants "floor" = none ∧
      program.externals "floor" = some (CMathCalls.floorExternal double)) →
    load heap (p.member "kind") = some (.integer 1) →
    load heap (p.member "mode") = some (.integer 4) →
    load heap (p.member "time") = some (.finite time) →
    StepArguments.Storage heap p buffers → StepEntry.InputsValid point (Binary64.toBits step).val time →
    load heap (p.member "stopDefined") = some (boolean stop.isSome) →
    (∀ value, stop = some value → load heap (p.member "stop") = some (.finite value)) →
    ¬ StepGuards.AboveStop (Binary64.addResult time step) stop →
    StepDiscard.Rejected time step →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock StepDiscard.message = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (StepEntry.outputHeap heap buffers time) message StepDiscard.message ∧
      StoredContents signed (pool.install before firstBlock signed)
        (StepEntry.outputHeap heap buffers time) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point (Binary64.toBits step).val flag buffers.outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (StepDiscard.arguments environment category message)
          (StepEntry.outputHeap heap buffers time) events value after ∧
          behavior = .terminates events ⟨.integer 2, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (StepDiscard.arguments environment category message)
          (StepEntry.outputHeap heap buffers time) events value after) ∧ behavior = .wrong []) := by
  exact tensor_discard_logged_for model m sigs stepMember (TensorFunctions.program model m sigs)
    (TensorFunctions.doStep_bound model m sigs unique stepMember)
    made before firstBlock signed heap frame context header

/-- Prepared constant rounding rejection: derive diagnostic/category addresses and
contents at callback entry, and retain every represented callback outcome.
Outputs are initialized before the terminated-mode write; neither write destroys literals.
No post-callback storage frame or native correspondence is claimed. -/
theorem constant_rounding_logged {source : AST.Model} {n : Nat} {E : Type}
    (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n) (sigs : List Signature)
    (stepMember : StepEntry.signature ∈ sigs)
    (unique : ((ConstantFunctions.functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    {pool : Pool (LiteralPreparation.excluded ++
      (ConstantFunctions.functions model m sigs).flatMap functionNames)}
    (made : ConstantFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)) (header : CFenv.Header) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (buffers : StepEntry.Buffers) (point step : BitVec 64) (time : Binary64.Value)
      (flag : Bool) (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
      (integer : context.target.types "int" = some .int32)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = ConstantFunctions.program model m sigs →
    context.target.constants "fegetround" = none →
    context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
    program.externals "fegetround" = some (CMathCalls.roundingExternal integer observed range) →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    load heap (p.member "time") = some (.finite time) →
    StepArguments.Storage heap p buffers → StepEntry.InputsValid point step time →
    observed ≠ header.nearest →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock StepFailures.roundingMessage = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) message StepFailures.roundingMessage ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point step flag buffers.outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after ∧
          behavior = .terminates events ⟨.integer 3, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after) ∧ behavior = .wrong []) := by
  letI : CInterface := context.target
  intro program p logger buffers point step time flag observed range integer environment name foreign linked
    ordinary macroBound rounding kindValue modeCell clock stored valid
    rejected loggerValue loggingValue environmentValue address external prototype
  have callbackFrame := frame.trans (stored.error_readonly time (some (.integer 4)) modeCell)
  obtain ⟨message, category, messageBound, categoryBound, messageStored, categoryStored⟩ :=
    PreparedNumericLiterals.constant_prepared model m sigs stepMember made before firstBlock signed
      (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) callbackFrame StepFailures.roundingMessage (Or.inl rfl)
  have defined : program.internal.definitions "fmi3DoStep" = some (.tree ConstantDoStep.function) := by
    rw [linked]
    exact ConstantFunctions.doStep_bound model m sigs unique stepMember
  have helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) := by
    rw [linked]
    exact ConstantFunctions.helpers_bound model m sigs Runtime.helpers[0]
      (by simp [ConstantFunctions.helpers, TensorFunctions.helpers])
  refine ⟨message, category, messageBound, categoryBound, messageStored, categoryStored, ?_⟩
  exact ConstantDoStep.rounding_rejection_contract.logged
    (pool.addresses firstBlock) context header program heap p message category logger buffers point step time flag
    observed range integer environment name foreign ordinary macroBound rounding defined helper messageBound
    address external prototype categoryBound kindValue modeCell clock stored valid rejected
    loggerValue loggingValue environmentValue

/-- Prepared constant stop rejection: derive diagnostic/category addresses and
contents at callback entry, and retain every represented callback outcome.
Outputs are initialized before the terminated-mode write; neither write destroys literals.
No post-callback storage frame or native correspondence is claimed. -/
theorem constant_stop_logged {source : AST.Model} {n : Nat} {E : Type}
    (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n) (sigs : List Signature)
    (stepMember : StepEntry.signature ∈ sigs)
    (unique : ((ConstantFunctions.functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    {pool : Pool (LiteralPreparation.excluded ++
      (ConstantFunctions.functions model m sigs).flatMap functionNames)}
    (made : ConstantFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)) (header : CFenv.Header) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (buffers : StepEntry.Buffers) (point : BitVec 64) (step time : Binary64.Value)
      (flag : Bool) (stop : Option Binary64.Value)
      (integer : context.target.types "int" = some .int32)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = ConstantFunctions.program model m sigs →
    context.target.constants "fegetround" = none →
    context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
    program.externals "fegetround" = some (CMathCalls.roundingExternal integer header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    load heap (p.member "time") = some (.finite time) →
    StepArguments.Storage heap p buffers → StepEntry.InputsValid point (Binary64.toBits step).val time →
    load heap (p.member "stopDefined") = some (boolean stop.isSome) →
    (∀ value, stop = some value → load heap (p.member "stop") = some (.finite value)) →
    StepGuards.AboveStop (Binary64.addResult time step) stop →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock StepFailures.stopMessage = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) message StepFailures.stopMessage ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point (Binary64.toBits step).val flag buffers.outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after ∧
          behavior = .terminates events ⟨.integer 3, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after) ∧ behavior = .wrong []) := by
  letI : CInterface := context.target
  intro program p logger buffers point step time flag stop integer environment name foreign linked
    ordinary macroBound rounding kindValue modeCell clock stored valid
    enabled limit rejected loggerValue loggingValue environmentValue address external prototype
  have callbackFrame := frame.trans (stored.error_readonly time (some (.integer 4)) modeCell)
  obtain ⟨message, category, messageBound, categoryBound, messageStored, categoryStored⟩ :=
    PreparedNumericLiterals.constant_prepared model m sigs stepMember made before firstBlock signed
      (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) callbackFrame StepFailures.stopMessage (Or.inr (Or.inl rfl))
  have defined : program.internal.definitions "fmi3DoStep" = some (.tree ConstantDoStep.function) := by
    rw [linked]
    exact ConstantFunctions.doStep_bound model m sigs unique stepMember
  have helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) := by
    rw [linked]
    exact ConstantFunctions.helpers_bound model m sigs Runtime.helpers[0]
      (by simp [ConstantFunctions.helpers, TensorFunctions.helpers])
  refine ⟨message, category, messageBound, categoryBound, messageStored, categoryStored, ?_⟩
  exact ConstantDoStep.stop_rejection_contract.logged
    (pool.addresses firstBlock) context header program heap p message category logger buffers point step time flag
    stop integer environment name foreign ordinary macroBound rounding defined helper messageBound categoryBound
    address external prototype kindValue modeCell clock stored valid enabled limit rejected
    loggerValue loggingValue environmentValue

/-- Prepared constant discard rejection: derive diagnostic/category addresses and
contents at callback entry, and retain every represented callback outcome.
No mode write, writable-mode premise, or failure-helper binding is required.
No post-callback storage frame or native correspondence is claimed. -/
theorem constant_discard_logged {source : AST.Model} {n : Nat} {E : Type}
    (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n) (sigs : List Signature)
    (stepMember : StepEntry.signature ∈ sigs)
    (unique : ((ConstantFunctions.functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    {pool : Pool (LiteralPreparation.excluded ++
      (ConstantFunctions.functions model m sigs).flatMap functionNames)}
    (made : ConstantFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)) (header : CFenv.Header) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (buffers : StepEntry.Buffers) (point : BitVec 64) (step time : Binary64.Value)
      (flag : Bool) (stop : Option Binary64.Value)
      (integer : context.target.types "int" = some .int32)
      (double : context.target.types "double" = some .float64)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = ConstantFunctions.program model m sigs →
    context.target.constants "fegetround" = none →
    context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
    context.target.constants "fmi3Discard" = some (.integer 2) →
    program.externals "fegetround" = some (CMathCalls.roundingExternal integer header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
    (StepGuards.Progress time (Binary64.addResult time step) →
      context.target.constants "floor" = none ∧
      program.externals "floor" = some (CMathCalls.floorExternal double)) →
    load heap (p.member "kind") = some (.integer 1) →
    load heap (p.member "mode") = some (.integer 4) →
    load heap (p.member "time") = some (.finite time) →
    StepArguments.Storage heap p buffers → StepEntry.InputsValid point (Binary64.toBits step).val time →
    load heap (p.member "stopDefined") = some (boolean stop.isSome) →
    (∀ value, stop = some value → load heap (p.member "stop") = some (.finite value)) →
    ¬ StepGuards.AboveStop (Binary64.addResult time step) stop →
    StepDiscard.Rejected time step →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock StepDiscard.message = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (StepEntry.outputHeap heap buffers time) message StepDiscard.message ∧
      StoredContents signed (pool.install before firstBlock signed)
        (StepEntry.outputHeap heap buffers time) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point (Binary64.toBits step).val flag buffers.outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (StepDiscard.arguments environment category message)
          (StepEntry.outputHeap heap buffers time) events value after ∧
          behavior = .terminates events ⟨.integer 2, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (StepDiscard.arguments environment category message)
          (StepEntry.outputHeap heap buffers time) events value after) ∧ behavior = .wrong []) := by
  letI : CInterface := context.target
  intro program p logger buffers point step time flag stop integer double environment name foreign linked
    ordinary macroBound discardBound rounding floorBound kindValue modeCell clock stored valid
    enabled limit noStop rejected loggerValue loggingValue environmentValue address external prototype
  have callbackFrame := frame.trans (stored.output_readonly time)
  obtain ⟨message, category, messageBound, categoryBound, messageStored, categoryStored⟩ :=
    PreparedNumericLiterals.constant_prepared model m sigs stepMember made before firstBlock signed
      (StepEntry.outputHeap heap buffers time) callbackFrame StepDiscard.message (Or.inr (Or.inr rfl))
  have defined : program.internal.definitions "fmi3DoStep" = some (.tree ConstantDoStep.function) := by
    rw [linked]
    exact ConstantFunctions.doStep_bound model m sigs unique stepMember
  refine ⟨message, category, messageBound, categoryBound, messageStored, categoryStored, ?_⟩
  exact ConstantDoStep.discard_rejection_contract.logged
    (pool.addresses firstBlock) context header program heap p message category logger buffers point step time flag
    stop integer double environment name foreign ordinary macroBound discardBound rounding floorBound defined
    kindValue modeCell clock stored valid enabled limit noStop rejected categoryBound messageBound
    address external prototype loggerValue loggingValue environmentValue


end Rumoca.FMI3.PreparedNumericFailureCall
