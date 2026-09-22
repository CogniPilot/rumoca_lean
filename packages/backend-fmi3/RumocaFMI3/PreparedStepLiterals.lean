import RumocaFMI3.TensorFunctions
import RumocaFMI3.ConstantFunctions
import RumocaFMI3.LoggingContract
import RumocaC.LiteralPoolContents

/-! lifecycle literals from the actual prepared function lists.
No event-program or callback behavior is asserted here. Installation constructs
symbolic storage; preservation of pre-existing base-heap objects would require
the separate fresh-block premise of `Pool.install_preserves`.
-/
namespace Rumoca.FMI3.PreparedLifecycleLiterals
open CTree CMemory CLiteral CStringMemory
set_option autoImplicit false
variable {source : AST.Model} {shape : Tensor.Shape} {n : Nat}

/-- The lifecycle diagnostic occurs in the shared guard itself. -/
theorem rejection_collected :
    ErrorCalls.rejectionMessage ∈ (Runtime.require .doStep).flatMap statementTexts := by
  simp [Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.reject,
    Runtime.branch, Runtime.fail, Runtime.ret, Runtime.call, Runtime.v,
    ErrorCalls.rejectionMessage, statementTexts, expressionTexts]

theorem tensor_rejection_collected (shape : Tensor.Shape) (hasOutput : Bool) :
    ErrorCalls.rejectionMessage ∈ functionTexts (TensorDoStep.function shape hasOutput) := by
  simp only [functionTexts, TensorDoStep.function, TensorDoStep.doStepBody,
    List.flatMap_append, List.mem_append, rejection_collected, true_or]

theorem constant_rejection_collected :
    ErrorCalls.rejectionMessage ∈ functionTexts ConstantDoStep.function := by
  simp only [functionTexts, ConstantDoStep.function, ConstantDoStep.doStepBody,
    List.flatMap_append, List.mem_append, rejection_collected, true_or]

/-- Both literals are derived from the same prepared tensor adapter list.
Only exact step-signature membership is needed; definition lookup uniqueness is
an independent premise for the later event-program composition.
-/
theorem tensor_prepared (model : Solve.FMI3Model source)
    (m : Solve.TensorFMI3Model shape) (sigs : List Signature)
    (step : StepEntry.signature ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++
      (TensorFunctions.functions model m sigs).flatMap functionNames)}
    (made : TensorFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap) :
    ∃ message category : Address,
      pool.addresses firstBlock ErrorCalls.rejectionMessage = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed) heap
        message ErrorCalls.rejectionMessage ∧
      StoredContents signed (pool.install before firstBlock signed) heap
        category "logStatus" := by
  have stepMember : TensorFunctions.tensorFunction model m StepEntry.signature ∈
      TensorFunctions.functions model m sigs :=
    List.mem_append_right _ (List.mem_map.mpr ⟨StepEntry.signature, step, rfl⟩)
  have occurs : ErrorCalls.rejectionMessage ∈ functionTexts
      (TensorFunctions.tensorFunction model m StepEntry.signature) :=
    tensor_rejection_collected shape m.hasOutput
  obtain ⟨message, messageBound⟩ := TensorFunctions.text_bound model m sigs made
    (TensorFunctions.tensorFunction model m StepEntry.signature) stepMember
    ErrorCalls.rejectionMessage occurs firstBlock
  obtain ⟨category, categoryBound⟩ := TensorFunctions.text_bound model m sigs made
    Runtime.helpers[0] (List.mem_append_left _ (by simp [TensorFunctions.helpers]))
    "logStatus" Logging.category_collected firstBlock
  exact ⟨message, category, messageBound, categoryBound,
    stored_contents pool before firstBlock signed heap frame _ _ messageBound,
    stored_contents pool before firstBlock signed heap frame _ _ categoryBound⟩

/-- Both literals are derived from the same prepared constant adapter list,
universally over the constant model and its state count.
-/
theorem constant_prepared (model : Solve.FMI3Model source)
    (m : Solve.ConstantFMI3Model n) (sigs : List Signature)
    (step : StepEntry.signature ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++
      (ConstantFunctions.functions model m sigs).flatMap functionNames)}
    (made : ConstantFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap) :
    ∃ message category : Address,
      pool.addresses firstBlock ErrorCalls.rejectionMessage = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed) heap
        message ErrorCalls.rejectionMessage ∧
      StoredContents signed (pool.install before firstBlock signed) heap
        category "logStatus" := by
  have stepMember : ConstantFunctions.constantFunction model m StepEntry.signature ∈
      ConstantFunctions.functions model m sigs :=
    List.mem_append_right _ (List.mem_map.mpr ⟨StepEntry.signature, step, rfl⟩)
  have occurs : ErrorCalls.rejectionMessage ∈ functionTexts
      (ConstantFunctions.constantFunction model m StepEntry.signature) :=
    constant_rejection_collected
  obtain ⟨message, messageBound⟩ := ConstantFunctions.text_bound model m sigs made
    (ConstantFunctions.constantFunction model m StepEntry.signature) stepMember
    ErrorCalls.rejectionMessage occurs firstBlock
  obtain ⟨category, categoryBound⟩ := ConstantFunctions.text_bound model m sigs made
    Runtime.helpers[0]
    (List.mem_append_left _ (by simp [ConstantFunctions.helpers, TensorFunctions.helpers]))
    "logStatus" Logging.category_collected firstBlock
  exact ⟨message, category, messageBound, categoryBound,
    stored_contents pool before firstBlock signed heap frame _ _ messageBound,
    stored_contents pool before firstBlock signed heap frame _ _ categoryBound⟩



end Rumoca.FMI3.PreparedLifecycleLiterals

/-! the two step-argument diagnostics and logging category come from
the actual prepared tensor/constant function lists. Literal storage and C-string
contents reuse `CLiteral.stored_contents`.

The frame starts at the installed heap. Installation need not preserve objects
already in `before` without the separate fresh-block premise. Category storage
does not establish callback execution, callback preservation, or native layout.
-/
namespace Rumoca.FMI3.PreparedArgumentLiterals
open CTree CMemory CLiteral
open CLiteral (StoredContents stored_contents)
set_option autoImplicit false
variable {source : AST.Model} {shape : Tensor.Shape} {n : Nat}

/-- Select either diagnostic by its text; its occurrence is proved from the
shared output/input guard syntax, not supplied as a membership hypothesis. -/
theorem message_collected (before after : List Stmt) (text : String)
    (selected : text = "Missing output pointer" ∨ text = StepArguments.inputMessage) :
    text ∈ (before ++ StepEntry.outputCode ++ StepEntry.inputGuard :: after).flatMap
      statementTexts := by
  rcases selected with rfl | rfl <;>
    simp [StepEntry.outputCode, StepEntry.inputGuard, StepArguments.inputMessage,
      Runtime.pointerCheck, Runtime.reject, Runtime.branch, Runtime.fail,
      Runtime.ret, Runtime.call, Runtime.v, statementTexts, expressionTexts]

theorem tensor_message_collected (shape : Tensor.Shape) (hasOutput : Bool)
    (text : String)
    (selected : text = "Missing output pointer" ∨ text = StepArguments.inputMessage) :
    text ∈ functionTexts (TensorDoStep.function shape hasOutput) := by
  have body : (TensorDoStep.function shape hasOutput).body =
      Runtime.require .doStep ++ StepEntry.outputCode ++ StepEntry.inputGuard ::
        (Runtime.stepRounding ++ Runtime.stepClock ++ Runtime.stepGrid ++
          TensorDoStep.tensorStepSolve shape hasOutput) := by
    simp [TensorDoStep.function, TensorDoStep.doStepBody, StepEntry.outputCode,
      StepEntry.inputGuard, StepEntry.inputCondition, List.append_assoc]
  rw [functionTexts, body]
  exact message_collected _ _ text selected

theorem constant_message_collected (text : String)
    (selected : text = "Missing output pointer" ∨ text = StepArguments.inputMessage) :
    text ∈ functionTexts ConstantDoStep.function := by
  have body : ConstantDoStep.function.body =
      Runtime.require .doStep ++ StepEntry.outputCode ++ StepEntry.inputGuard ::
        (Runtime.stepRounding ++ Runtime.stepClock ++ Runtime.stepGrid ++
          ConstantDoStep.stepSolve) := by
    simp [ConstantDoStep.function, ConstantDoStep.doStepBody, StepEntry.outputCode,
      StepEntry.inputGuard, StepEntry.inputCondition, List.append_assoc]
  rw [functionTexts, body]
  exact message_collected _ _ text selected

/-- Any tensor model, including either output choice, supplies both selected
argument diagnostics and the helper's category through its actual prepared pool.
No definition-table uniqueness or successful call is needed for literal binding.
-/
theorem tensor_prepared (model : Solve.FMI3Model source)
    (m : Solve.TensorFMI3Model shape) (sigs : List Signature)
    (step : StepEntry.signature ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++
      (TensorFunctions.functions model m sigs).flatMap functionNames)}
    (made : TensorFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (text : String)
    (selected : text = "Missing output pointer" ∨ text = StepArguments.inputMessage) :
    ∃ message category : Address,
      pool.addresses firstBlock text = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed) heap message text ∧
      StoredContents signed (pool.install before firstBlock signed) heap category "logStatus" := by
  have stepMember : TensorFunctions.tensorFunction model m StepEntry.signature ∈
      TensorFunctions.functions model m sigs :=
    List.mem_append_right _ (List.mem_map.mpr ⟨StepEntry.signature, step, rfl⟩)
  have occurs : text ∈ functionTexts
      (TensorFunctions.tensorFunction model m StepEntry.signature) :=
    tensor_message_collected shape m.hasOutput text selected
  obtain ⟨message, messageBound⟩ := TensorFunctions.text_bound model m sigs made
    (TensorFunctions.tensorFunction model m StepEntry.signature) stepMember text occurs firstBlock
  obtain ⟨category, categoryBound⟩ := TensorFunctions.text_bound model m sigs made
    Runtime.helpers[0] (List.mem_append_left _ (by simp [TensorFunctions.helpers]))
    "logStatus" Logging.category_collected firstBlock
  exact ⟨message, category, messageBound, categoryBound,
    stored_contents pool before firstBlock signed heap frame _ _ messageBound,
    stored_contents pool before firstBlock signed heap frame _ _ categoryBound⟩

/-- The same selected diagnostics/category for every constant model and count,
with the same pool, installation parameters and later read-only frame. -/
theorem constant_prepared (model : Solve.FMI3Model source)
    (m : Solve.ConstantFMI3Model n) (sigs : List Signature)
    (step : StepEntry.signature ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++
      (ConstantFunctions.functions model m sigs).flatMap functionNames)}
    (made : ConstantFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (text : String)
    (selected : text = "Missing output pointer" ∨ text = StepArguments.inputMessage) :
    ∃ message category : Address,
      pool.addresses firstBlock text = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed) heap message text ∧
      StoredContents signed (pool.install before firstBlock signed) heap category "logStatus" := by
  have stepMember : ConstantFunctions.constantFunction model m StepEntry.signature ∈
      ConstantFunctions.functions model m sigs :=
    List.mem_append_right _ (List.mem_map.mpr ⟨StepEntry.signature, step, rfl⟩)
  have occurs : text ∈ functionTexts
      (ConstantFunctions.constantFunction model m StepEntry.signature) :=
    constant_message_collected text selected
  obtain ⟨message, messageBound⟩ := ConstantFunctions.text_bound model m sigs made
    (ConstantFunctions.constantFunction model m StepEntry.signature) stepMember text occurs firstBlock
  obtain ⟨category, categoryBound⟩ := ConstantFunctions.text_bound model m sigs made
    Runtime.helpers[0]
    (List.mem_append_left _ (by simp [ConstantFunctions.helpers, TensorFunctions.helpers]))
    "logStatus" Logging.category_collected firstBlock
  exact ⟨message, category, messageBound, categoryBound,
    stored_contents pool before firstBlock signed heap frame _ _ messageBound,
    stored_contents pool before firstBlock signed heap frame _ _ categoryBound⟩



end Rumoca.FMI3.PreparedArgumentLiterals

/-! rounding, stop and discard diagnostics bound to the actual prepared
tensor/constant step function lists. 

Storage and C-string contents reuse `CLiteral.stored_contents`.
The supplied read-only frame starts at installation; preserving pre-existing
base-heap objects during installation separately requires fresh literal blocks.
No whole-call, callback-frame, native-layout or actual-artifact claim is made.
-/
namespace Rumoca.FMI3.PreparedNumericLiterals
open CTree CMemory CLiteral
open CLiteral (StoredContents stored_contents)
set_option autoImplicit false
variable {source : AST.Model} {shape : Tensor.Shape} {n : Nat}

/-- Each selected diagnostic occurs in the shared rounding/clock guards.
The discard occurrence is inside the clock's logging branch, before the grid
tail; no diagnostic-membership premise or numerical execution is assumed. -/
theorem message_collected (before after : List Stmt) (text : String)
    (selected : text = StepFailures.roundingMessage ∨ text = StepFailures.stopMessage ∨
      text = StepDiscard.message) :
    text ∈ (before ++ Runtime.stepRounding ++ Runtime.stepClock ++ after).flatMap
      statementTexts := by
  rcases selected with rfl | rfl | rfl <;>
    simp [Runtime.stepRounding, Runtime.stepClock, Runtime.stepDiscard, Runtime.log,
      Runtime.reject, Runtime.branch, Runtime.fail, Runtime.ret, Runtime.call, Runtime.v,
      StepFailures.roundingMessage, StepFailures.stopMessage, StepDiscard.message,
      statementTexts, expressionTexts]

theorem tensor_message_collected (shape : Tensor.Shape) (hasOutput : Bool)
    (text : String)
    (selected : text = StepFailures.roundingMessage ∨ text = StepFailures.stopMessage ∨
      text = StepDiscard.message) :
    text ∈ functionTexts (TensorDoStep.function shape hasOutput) := by
  have body : (TensorDoStep.function shape hasOutput).body =
      (Runtime.require .doStep ++ StepEntry.outputCode ++ [StepEntry.inputGuard]) ++
        Runtime.stepRounding ++ Runtime.stepClock ++
          (Runtime.stepGrid ++ TensorDoStep.tensorStepSolve shape hasOutput) := by
    simp [TensorDoStep.function, TensorDoStep.doStepBody, StepEntry.outputCode,
      StepEntry.inputGuard, StepEntry.inputCondition, List.append_assoc]
  rw [functionTexts, body]
  exact message_collected _ _ text selected

theorem constant_message_collected (text : String)
    (selected : text = StepFailures.roundingMessage ∨ text = StepFailures.stopMessage ∨
      text = StepDiscard.message) :
    text ∈ functionTexts ConstantDoStep.function := by
  have body : ConstantDoStep.function.body =
      (Runtime.require .doStep ++ StepEntry.outputCode ++ [StepEntry.inputGuard]) ++
        Runtime.stepRounding ++ Runtime.stepClock ++
          (Runtime.stepGrid ++ ConstantDoStep.stepSolve) := by
    simp [ConstantDoStep.function, ConstantDoStep.doStepBody, StepEntry.outputCode,
      StepEntry.inputGuard, StepEntry.inputCondition, List.append_assoc]
  rw [functionTexts, body]
  exact message_collected _ _ text selected

/-- The selected diagnostic and category use the same actual tensor pool and
installation/frame parameters, for every model and shape/output choice. -/
theorem tensor_prepared (model : Solve.FMI3Model source)
    (m : Solve.TensorFMI3Model shape) (sigs : List Signature)
    (step : StepEntry.signature ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++
      (TensorFunctions.functions model m sigs).flatMap functionNames)}
    (made : TensorFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (text : String)
    (selected : text = StepFailures.roundingMessage ∨ text = StepFailures.stopMessage ∨
      text = StepDiscard.message) :
    ∃ message category : Address,
      pool.addresses firstBlock text = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed) heap message text ∧
      StoredContents signed (pool.install before firstBlock signed) heap category "logStatus" := by
  have stepMember : TensorFunctions.tensorFunction model m StepEntry.signature ∈
      TensorFunctions.functions model m sigs :=
    List.mem_append_right _ (List.mem_map.mpr ⟨StepEntry.signature, step, rfl⟩)
  have occurs : text ∈ functionTexts
      (TensorFunctions.tensorFunction model m StepEntry.signature) :=
    tensor_message_collected shape m.hasOutput text selected
  obtain ⟨message, messageBound⟩ := TensorFunctions.text_bound model m sigs made
    (TensorFunctions.tensorFunction model m StepEntry.signature) stepMember text occurs firstBlock
  obtain ⟨category, categoryBound⟩ := TensorFunctions.text_bound model m sigs made
    Runtime.helpers[0] (List.mem_append_left _ (by simp [TensorFunctions.helpers]))
    "logStatus" Logging.category_collected firstBlock
  exact ⟨message, category, messageBound, categoryBound,
    stored_contents pool before firstBlock signed heap frame _ _ messageBound,
    stored_contents pool before firstBlock signed heap frame _ _ categoryBound⟩

/-- The same selected diagnostic/category guarantee for arbitrary constant
models and state counts, with no assumed diagnostic occurrence. -/
theorem constant_prepared (model : Solve.FMI3Model source)
    (m : Solve.ConstantFMI3Model n) (sigs : List Signature)
    (step : StepEntry.signature ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++
      (ConstantFunctions.functions model m sigs).flatMap functionNames)}
    (made : ConstantFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (text : String)
    (selected : text = StepFailures.roundingMessage ∨ text = StepFailures.stopMessage ∨
      text = StepDiscard.message) :
    ∃ message category : Address,
      pool.addresses firstBlock text = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed) heap message text ∧
      StoredContents signed (pool.install before firstBlock signed) heap category "logStatus" := by
  have stepMember : ConstantFunctions.constantFunction model m StepEntry.signature ∈
      ConstantFunctions.functions model m sigs :=
    List.mem_append_right _ (List.mem_map.mpr ⟨StepEntry.signature, step, rfl⟩)
  have occurs : text ∈ functionTexts
      (ConstantFunctions.constantFunction model m StepEntry.signature) :=
    constant_message_collected text selected
  obtain ⟨message, messageBound⟩ := ConstantFunctions.text_bound model m sigs made
    (ConstantFunctions.constantFunction model m StepEntry.signature) stepMember text occurs firstBlock
  obtain ⟨category, categoryBound⟩ := ConstantFunctions.text_bound model m sigs made
    Runtime.helpers[0]
    (List.mem_append_left _ (by simp [ConstantFunctions.helpers, TensorFunctions.helpers]))
    "logStatus" Logging.category_collected firstBlock
  exact ⟨message, category, messageBound, categoryBound,
    stored_contents pool before firstBlock signed heap frame _ _ messageBound,
    stored_contents pool before firstBlock signed heap frame _ _ categoryBound⟩



end Rumoca.FMI3.PreparedNumericLiterals
