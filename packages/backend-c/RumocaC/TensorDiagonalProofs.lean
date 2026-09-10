import RumocaC.TensorDiagonalMemory
import RumocaC.TensorDiagonalCode
import RumocaC.TensorFillProofs
import RumocaC.TensorProgramParameters

/-! Execute the actual diagonal copy loop and its local declarations.
The internal loop theorem takes its arithmetic step compositionally;
`offset_eval` discharges it with the authored unsigned-addition semantics. -/
noncomputable section
namespace Rumoca.CTensor.Diagonal
open CTree CMemory CMemory.TensorView Rumoca.Tensor
variable [interface : CInterface]
set_option maxRecDepth 10000

def arguments (input output : Address) (shape : Shape) : Lowering.Arguments.Values := fun name =>
  if name = "coeff" then .pointer (some input)
  else if name = "out" then .pointer (some output)
  else if name = "count" then .integer shape.volume
  else .integer (matrixShape shape.volume shape.volume).volume

def parameters (input output : Address) (shape : Shape) : CBody.Locals :=
  Lowering.Arguments.locals signatureParameters (arguments input output shape)

def parameterTypes : CLoops.Types := Lowering.Arguments.types signatureParameters

def localTypes : CLoops.Types :=
  CLoops.bindType (CLoops.bindType (CLoops.bindType parameterTypes "offset" .size) "stride" .size) "k" .size

def locals (input output : Address) (shape : Shape) (i : Nat) : CBody.Locals :=
  CBody.bind (CBody.bind (parameters input output shape) "stride" (.integer (shape.volume + 1)))
    "offset" (.integer (position shape i))

omit interface in
theorem bind_valid (input output : Address) (shape : Shape)
    (bounded : (matrixShape shape.volume shape.volume).volume < 2 ^ 64) :
    Lowering.Arguments.Valid signatureParameters (arguments input output shape) := by
  intro p member
  simp only [signatureParameters, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact .input _
  · exact .output _
  · exact .count shape.volume (counter_bounds shape bounded).1
  · exact .count _ bounded

theorem copy_step (input output : Address) (values : Values shape) (heap : Heap)
    (separate : Separate output input shape) (reads : Reads heap input values)
    (i : Fin shape.volume) (rest : List Stmt) :
    CLoops.next (.running (.assign (.index (.id "out") (.id "offset")) (indexed "coeff") :: rest)
      (CLoops.counterEnv (locals input output shape i.val) "k" i.val) localTypes
      (scatter (zeroHeap heap output shape) output values i.val)) =
      some (.running rest (CLoops.counterEnv (locals input output shape i.val) "k" i.val) localTypes
        (scatter (zeroHeap heap output shape) output values (i.val + 1))) := by
  have value := index_eval (CLoops.counterEnv (locals input output shape i.val) "k" i.val)
    (scatter (zeroHeap heap output shape) output values i.val) "coeff" input i.val
    (by simp [CLoops.counterEnv, locals, parameters, Lowering.Arguments.locals, signatureParameters,
      arguments, CBody.bind]) (by simp [CLoops.counterEnv, CBody.bind])
  rw [input_reads heap output input values i.val separate reads i] at value
  have target : CBody.lvalue (CLoops.counterEnv (locals input output shape i.val) "k" i.val)
      (scatter (zeroHeap heap output shape) output values i.val)
      (.index (.id "out") (.id "offset")) = some (output.index (position shape i.val)) := by
    simp [CBody.lvalue, CBody.eval, CBody.resolve, CLoops.counterEnv, locals, parameters,
      Lowering.Arguments.locals, signatureParameters, arguments, CBody.bind, Value.address]
  have stored := scatter_store_next (zeroHeap heap output shape) output values (zero_writable heap output shape) i
  have evaluated : CLoops.eval (CLoops.counterEnv (locals input output shape i.val) "k" i.val)
      localTypes (scatter (zeroHeap heap output shape) output values i.val) (indexed "coeff") =
      some (.finite values[i]) := value
  simp only [CLoops.next, evaluated, target, stored, bind, Option.bind_some, pure]

theorem offset_eval (input output : Address) (shape : Shape) (heap : Heap)
    (bounded : (matrixShape shape.volume shape.volume).volume < 2 ^ 64)
    (i : Nat) (hi : i < shape.volume) :
    CLoops.eval (CLoops.counterEnv (locals input output shape i) "k" i) localTypes heap
      (.bin .add (.id "offset") (.id "stride")) = some (.integer (position shape (i + 1))) := by
  have additionBound : position shape i + (shape.volume + 1) < 2 ^ 64 := by
    simpa only [position, Nat.add_mul, Nat.one_mul] using position_bounded shape bounded (i + 1) (by omega)
  have evaluated := CLoops.eval_sizeAdd (CLoops.counterEnv (locals input output shape i) "k" i)
    localTypes heap "offset" "stride" (position shape i) (shape.volume + 1)
    (by simp [CLoops.counterEnv, locals, CBody.bind])
    (by simp [CLoops.counterEnv, locals, CBody.bind, Nat.cast_add, Nat.cast_one])
    (by simp [localTypes, CLoops.bindType]) (by simp [localTypes, CLoops.bindType]) additionBound
  simpa only [position, Nat.add_mul, Nat.one_mul] using evaluated

theorem offset_step (input output : Address) (shape : Shape) (heap : Heap) (i : Nat)
    (bound : position shape (i + 1) < 2 ^ 64) (rest : List Stmt)
    (evaluated : CLoops.eval (CLoops.counterEnv (locals input output shape i) "k" i) localTypes heap
      (.bin .add (.id "offset") (.id "stride")) = some (.integer (position shape (i + 1)))) :
    CLoops.next (.running (.assign (.id "offset") (.bin .add (.id "offset") (.id "stride")) :: rest)
      (CLoops.counterEnv (locals input output shape i) "k" i) localTypes heap) =
      some (.running rest (CLoops.counterEnv (locals input output shape (i + 1)) "k" i) localTypes heap) := by
  have changed : CBody.bind (CLoops.counterEnv (locals input output shape i) "k" i)
      "offset" (.integer (position shape (i + 1))) =
      CLoops.counterEnv (locals input output shape (i + 1)) "k" i := by
    funext name
    by_cases hk : name = "k"
    · subst name; simp [CLoops.counterEnv, CBody.bind]
    · by_cases ho : name = "offset"
      · subst name; simp [CLoops.counterEnv, locals, CBody.bind]
      · simp [CLoops.counterEnv, locals, CBody.bind, hk, ho]
  have step := CLoops.assign_local (CLoops.counterEnv (locals input output shape i) "k" i) localTypes
    heap "offset" (.bin .add (.id "offset") (.id "stride")) rest (.integer (position shape i))
    (.integer (position shape (i + 1))) (.integer (position shape (i + 1))) .size
    (by simp [CLoops.counterEnv, locals, CBody.bind]) (by simp [localTypes, CLoops.bindType])
    evaluated (CLoops.convert_size_nat _ bound)
  simpa only [changed] using step

theorem loop_reaches (input output : Address) (values : Values shape) (heap : Heap)
    (separate : Separate output input shape) (reads : Reads heap input values)
    (bounded : (matrixShape shape.volume shape.volume).volume < 2 ^ 64)
    (addition : ∀ i < shape.volume, CLoops.eval
      (CLoops.counterEnv (locals input output shape i) "k" i) localTypes
      (scatter (zeroHeap heap output shape) output values (i + 1))
      (.bin .add (.id "offset") (.id "stride")) = some (.integer (position shape (i + 1)))) :
    Transition.Reaches CLoops.machine.step
      (.running [CLoops.loop "k" (.id "count") operation, .ret none]
        (CLoops.counterEnv (locals input output shape 0) "k" 0) localTypes (zeroHeap heap output shape))
      (.returned ⟨.void, resultHeap heap output values⟩) := by
  have repeated := CLoops.loop_reaches "k" (.id "count") operation [.ret none]
    (locals input output shape) localTypes (scatter (zeroHeap heap output shape) output values)
    shape.volume (by simp [localTypes, CLoops.bindType]) (counter_bounds shape bounded).1
    (by simp [operation, CLoops.noDeclarations])
    (by
      intro i hi
      simp [CBody.eval, CBody.resolve, CLoops.counterEnv, locals, parameters,
        Lowering.Arguments.locals, signatureParameters, arguments, CBody.bind])
    (by
      intro i hi
      exact .next (copy_step input output values heap separate reads ⟨i, hi⟩ _)
        (.next (offset_step input output shape _ i (position_bounded shape bounded (i + 1) (by omega))
          _ (addition i hi)) (.refl _)))
  exact repeated.trans (.next rfl (.refl _))

theorem initialize_reaches (input output : Address) (shape : Shape) (heap : Heap)
    (bounded : (matrixShape shape.volume shape.volume).volume < 2 ^ 64)
    (sizeType : interface.types "size_t" = some .size) :
    Transition.Reaches CLoops.machine.step
      (.running tail (parameters input output shape) parameterTypes (zeroHeap heap output shape))
      (.running [CLoops.loop "k" (.id "count") operation, .ret none]
        (CLoops.counterEnv (locals input output shape 0) "k" 0) localTypes (zeroHeap heap output shape)) := by
  have startK := CLoops.counter_initialize (locals input output shape 0)
    (CLoops.bindType (CLoops.bindType parameterTypes "offset" .size) "stride" .size)
    (zeroHeap heap output shape) "k" [CLoops.loop "k" (.id "count") operation, .ret none]
    (by simp [locals, parameters, Lowering.Arguments.locals, signatureParameters, CBody.bind]) sizeType
  let envOffset := CLoops.counterEnv (parameters input output shape) "offset" 0
  let typeOffset := CLoops.bindType parameterTypes "offset" .size
  have evaluated := CLoops.eval_increment envOffset typeOffset (zeroHeap heap output shape) "count"
    shape.volume (by simp [envOffset, CLoops.counterEnv, parameters, Lowering.Arguments.locals,
      signatureParameters, arguments, CBody.bind])
    (by simp [typeOffset, parameterTypes, Lowering.Arguments.types, signatureParameters, CLoops.bindType,
      Lowering.Arguments.type]) (counter_bounds shape bounded).2.1
  have swapped : CBody.bind envOffset "stride" (.integer (shape.volume + 1)) =
      locals input output shape 0 := by
    funext name
    by_cases hs : name = "stride"
    · subst name; simp [envOffset, locals, CBody.bind]
    · by_cases ho : name = "offset"
      · subst name; simp [envOffset, CLoops.counterEnv, locals, CBody.bind, position]
      · simp [envOffset, CLoops.counterEnv, locals, CBody.bind, hs, ho]
  have strideFresh : envOffset "stride" = none := by
    simp [envOffset, CLoops.counterEnv, parameters, Lowering.Arguments.locals, signatureParameters, CBody.bind]
  have converted := CLoops.convert_size_nat (shape.volume + 1) (counter_bounds shape bounded).2.1
  simp only [Nat.cast_add, Nat.cast_one] at converted
  have startStride : CLoops.next (.running
      (.declare "size_t" "stride" (.bin .add (.id "count") (.nat 1)) ::
        CLoops.counted "k" (.id "count") operation ++ [.ret none]) envOffset typeOffset
      (zeroHeap heap output shape)) = some (.running
        (CLoops.counted "k" (.id "count") operation ++ [.ret none]) (locals input output shape 0)
        (CLoops.bindType typeOffset "stride" .size) (zeroHeap heap output shape)) := by
    have declared := CLoops.declare_local envOffset typeOffset (zeroHeap heap output shape)
      "size_t" "stride" (.bin .add (.id "count") (.nat 1))
      (CLoops.counted "k" (.id "count") operation ++ [.ret none]) .size
      (.integer (shape.volume + 1)) (.integer (shape.volume + 1)) sizeType strideFresh evaluated converted
    simpa only [List.cons_append, swapped] using declared
  have startOffset := CLoops.counter_initialize (parameters input output shape) parameterTypes
    (zeroHeap heap output shape) "offset"
    (.declare "size_t" "stride" (.bin .add (.id "count") (.nat 1)) ::
      CLoops.counted "k" (.id "count") operation ++ [.ret none])
    (by simp [parameters, Lowering.Arguments.locals, signatureParameters, CBody.bind]) sizeType
  exact .next startOffset (.next startStride (.next startK (.refl _)))

theorem tail_reaches (input output : Address) (values : Values shape) (heap : Heap)
    (separate : Separate output input shape) (reads : Reads heap input values)
    (bounded : (matrixShape shape.volume shape.volume).volume < 2 ^ 64)
    (sizeType : interface.types "size_t" = some .size)
    (addition : ∀ i < shape.volume, CLoops.eval
      (CLoops.counterEnv (locals input output shape i) "k" i) localTypes
      (scatter (zeroHeap heap output shape) output values (i + 1))
      (.bin .add (.id "offset") (.id "stride")) = some (.integer (position shape (i + 1)))) :
    Transition.Reaches CLoops.machine.step
      (.running tail (parameters input output shape) parameterTypes (zeroHeap heap output shape))
      (.returned ⟨.void, resultHeap heap output values⟩) := by
  exact (initialize_reaches input output shape heap bounded sizeType).trans
    (loop_reaches input output values heap separate reads bounded addition)

end Rumoca.CTensor.Diagonal
