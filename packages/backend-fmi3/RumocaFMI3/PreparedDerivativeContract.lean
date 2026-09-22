import RumocaFMI3.PreparedStepLiterals

/-! Bind the checked derivative entry and its diagnostic to the same prepared
adapter text, definition table and literal pool. Callback effects and native
floating-environment correspondence remain explicit boundaries. -/
namespace Rumoca.FMI3.PreparedDerivative
open CTree CMemory CLiteral CStringMemory
variable {source : AST.Model} {shape : Tensor.Shape}

theorem message_collected (shape : Tensor.Shape) (hasOutput : Bool) :
    TensorDerivativePreflight.message ∈
      functionTexts (TensorContinuousStates.derivFunction shape hasOutput) := by
  simp [functionTexts, TensorContinuousStates.derivFunction,
    TensorContinuousStates.derivCheckedFunction, TensorContinuousStates.derivCheckedBody,
    TensorDerivativePreflight.body, TensorDerivativePreflight.reject, Discard.body,
    Runtime.log, Runtime.branch, Runtime.ret, Runtime.v, Runtime.field,
    Runtime.both, Runtime.nev, statementTexts, expressionTexts]

theorem prepared (model : Solve.FMI3Model source)
    (m : Solve.TensorFMI3Model shape) (sigs : List Signature)
    (member : DerivativeCalls.signature ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++
      (TensorFunctions.functions model m sigs).flatMap functionNames)}
    (made : TensorFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap) :
    ∃ message category : Address,
      pool.addresses firstBlock TensorDerivativePreflight.message = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed) heap
        message TensorDerivativePreflight.message ∧
      StoredContents signed (pool.install before firstBlock signed) heap
        category "logStatus" := by
  have fnMember : TensorFunctions.tensorFunction model m DerivativeCalls.signature ∈
      TensorFunctions.functions model m sigs :=
    List.mem_append_right _ (List.mem_map.mpr ⟨DerivativeCalls.signature, member, rfl⟩)
  have occurs : TensorDerivativePreflight.message ∈ functionTexts
      (TensorFunctions.tensorFunction model m DerivativeCalls.signature) :=
    message_collected shape m.hasOutput
  obtain ⟨message, messageBound⟩ := TensorFunctions.text_bound model m sigs made
    (TensorFunctions.tensorFunction model m DerivativeCalls.signature) fnMember
    TensorDerivativePreflight.message occurs firstBlock
  obtain ⟨category, categoryBound⟩ := TensorFunctions.text_bound model m sigs made
    Runtime.helpers[0] (List.mem_append_left _ (by simp [TensorFunctions.helpers]))
    "logStatus" Logging.category_collected firstBlock
  exact ⟨message, category, messageBound, categoryBound,
    stored_contents pool before firstBlock signed heap frame _ _ messageBound,
    stored_contents pool before firstBlock signed heap frame _ _ categoryBound⟩

structure Contract (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List Signature) : Prop where
  member : DerivativeCalls.signature ∈ sigs
  defined : (TensorFunctions.program model m sigs).definitions "fmi3GetContinuousStateDerivatives" =
    some (.tree (TensorContinuousStates.derivFunction shape m.hasOutput))
  rendered : ∃ before after : String, TensorFunctions.render model m sigs =
    before ++ (TensorContinuousStates.derivFunction shape m.hasOutput).render ++ after
  literals : ∀ (pool : Pool (LiteralPreparation.excluded ++
      (TensorFunctions.functions model m sigs).flatMap functionNames)),
    TensorFunctions.prepare model m sigs = some pool →
    ∀ (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap),
    CReadOnly.Preserves (pool.install before firstBlock signed) heap →
    ∃ message category : Address,
      pool.addresses firstBlock TensorDerivativePreflight.message = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed) heap
        message TensorDerivativePreflight.message ∧
      StoredContents signed (pool.install before firstBlock signed) heap category "logStatus"

theorem contract (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List Signature)
    (member : DerivativeCalls.signature ∈ sigs)
    (unique : ((TensorFunctions.functions model m sigs).map (fun fn => fn.signature.name)).Nodup) :
    Contract model m sigs where
  member := member
  defined := TensorFunctions.function_bound model m sigs unique DerivativeCalls.signature member
  rendered := TensorFunctions.rendered_member model m sigs DerivativeCalls.signature member
  literals _pool made := prepared model m sigs member made

end Rumoca.FMI3.PreparedDerivative
