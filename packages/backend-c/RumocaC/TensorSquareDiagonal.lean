import RumocaC.TensorDiagonalCalls
import RumocaC.AdditionResults
import RumocaCore.Array.Finite

/-! Scratch-free dense Jacobian materializer for the square kernel `der(x) = u .* u`.

The Jacobian of the pointwise square is the diagonal matrix `diag(2*u)`; every
off-diagonal entry is zero. This helper writes that dense matrix directly from the
input tensor `u`, with no intermediate coefficient buffer: it zero-fills the output
region with the shared `rumoca_tensor_fill` helper and then, in one counted loop,
stores `u[k] + u[k]` at the diagonal cell `k * (count + 1)` of the row-major matrix.

The whole computation reuses the diagonal-copy memory model of
`Rumoca.CTensor.Diagonal` (`scatter`, `zeroHeap`, `resultHeap`, `matrix`,
`result_reads`, `result_frame`, `scatter_store_next`, `offset_step`): the only new
step is that the stored value on the diagonal is the finite sum `u[k] + u[k]`
rather than a copied coefficient. The written diagonal is related to the prepared
AD Jacobian program (`ArrayProfile.squareJacobianProgram`) by
`diagonal_nearest`: each stored entry is a nearest finite value to `2 * u[k]`, the
exact diagonal of the real Jacobian `AD.squareJacobian`.

This is a package-checked reusable helper. It emits no production artifact on its
own and changes no existing contract; the tensor FMI adapter binding remains a
separate step. -/
noncomputable section
namespace Rumoca.CTensor.SquareDiagonal
open CTree CMemory CMemory.TensorView Rumoca.Tensor
open Rumoca.CTensor.Diagonal (scatter zeroHeap resultHeap position matrix result_reads result_frame
  scatter_store_next zero_writable offset_step offset_eval signatureParameters
  locals arguments bind_valid position_bound position_bounded counter_bounds)
variable [interface : CInterface]
set_option maxRecDepth 10000

/-- The diagonal value written for each state coordinate: the finite sum
`u[k] + u[k]`, materialized as the diagonal vector `2*u`. -/
def doubled (values : Values shape) : Values shape := Value.zipWith Binary64.roundedAdd values values

omit interface in
@[simp] theorem doubled_get (values : Values shape) (i : Fin shape.volume) :
    (doubled values)[i] = Binary64.roundedAdd values[i] values[i] :=
  Value.getElem_zipWith _ _ _ i.isLt

/-- The counted diagonal loop body: `out[offset] = coeff[k] + coeff[k]; offset += stride`. -/
def operation : List Stmt :=
  [.assign (.index (.id "out") (.id "offset")) (.bin .add (indexed "coeff") (indexed "coeff")),
   .assign (.id "offset") (.bin .add (.id "offset") (.id "stride"))]

/-- Zero-fill the output then run the diagonal loop; the offset and stride locals
are declared once at function scope, as in the diagonal-copy helper. -/
def tail : List Stmt :=
  [.declare "size_t" "offset" (.nat 0),
   .declare "size_t" "stride" (.bin .add (.id "count") (.nat 1))] ++
  CLoops.counted "k" (.id "count") operation ++ [.ret none]

/-- The reusable square-Jacobian materializer. Its signature matches the diagonal
helper (`coeff`, `out`, `count`, `cells`); only the loop value differs. -/
def function : Function where
  signature := ⟨"void", "rumoca_square_jacobian_diag", signatureParameters.map Lowering.Syntax.Parameter.tree⟩
  body := Fill.invoke (CAlgorithm.literal .zero) (.id "out") (.id "cells") :: tail
  static := false

/-- Call the helper, materializing `diag(2*coeff)` into `output`. -/
def invoke (coeff output count cells : Expr) : Stmt :=
  .eval (.call (.id function.signature.name) [coeff, output, count, cells])

omit interface in
theorem signature_eq : function.signature.parameters = Diagonal.function.signature.parameters := rfl

omit interface in
/-- The input region is preserved by the zero-fill and by every diagonal store,
since the output positions are disjoint from the input. Generalizes
`Diagonal.input_reads` to a scattered diagonal (`result`) distinct from the read
input values. -/
theorem coeff_reads (heap : Heap) (output input : Address) (result values : Values shape) (k : Nat)
    (separate : Diagonal.Separate output input shape) (reads : Reads heap input values) :
    Reads (scatter (zeroHeap heap output shape) output result k) input values := by
  intro i
  have copied := Diagonal.scatter_frame (zeroHeap heap output shape) output result k (input.index i.val)
    (fun j hj => Ne.symm (separate _ (position_bound ⟨j, hj⟩) i.val i.isLt))
  have zeroed := written_frame heap output
    (Tensor.Value.fill (matrixShape shape.volume shape.volume) Binary64.positiveZero)
    (matrixShape shape.volume shape.volume).volume (input.index i.val)
    (fun j hj => Ne.symm (separate j hj i.val i.isLt))
  simp only [load, copied]
  simpa only [zeroHeap, zeroed, load] using reads i

/-- One diagonal iteration reads the input cell `coeff[k]` twice, forms the finite
sum `u[k] + u[k]`, and stores it at the diagonal cell `k * (count + 1)`, advancing
the scattered diagonal by one entry. The finite outcome of the doubled cell is the
explicit premise `adds`. -/
theorem copy_step (output input : Address) (result values : Values shape) (heap : Heap)
    (separate : Diagonal.Separate output input shape) (reads : Reads heap input values)
    (adds : ∀ i : Fin shape.volume, Binary64.Adds values[i] values[i] (.finite result[i]))
    (i : Fin shape.volume) (rest : List Stmt) :
    CLoops.next (.running (operation ++ rest)
      (CLoops.counterEnv (locals input output shape i.val) "k" i.val) Diagonal.localTypes
      (scatter (zeroHeap heap output shape) output result i.val)) =
      some (.running (.assign (.id "offset") (.bin .add (.id "offset") (.id "stride")) :: rest)
        (CLoops.counterEnv (locals input output shape i.val) "k" i.val) Diagonal.localTypes
        (scatter (zeroHeap heap output shape) output result (i.val + 1))) := by
  set env := CLoops.counterEnv (locals input output shape i.val) "k" i.val with henv
  set H := scatter (zeroHeap heap output shape) output result i.val with hH
  have coeffPtr : env "coeff" = some (.pointer (some input)) := by
    simp [henv, CLoops.counterEnv, locals, Diagonal.parameters, Lowering.Arguments.locals, signatureParameters,
      arguments, CBody.bind]
  have counter : env "k" = some (.integer i.val) := by simp [henv, CLoops.counterEnv, CBody.bind]
  have coeffLoad : load H (input.index i.val) = some (.finite values[i]) :=
    coeff_reads heap output input result values i.val separate reads i
  have coeffEval : CBody.eval env H (indexed "coeff") = some (.finite values[i]) :=
    (Rumoca.CTensor.index_eval env H "coeff" input i.val coeffPtr counter).trans coeffLoad
  have rhs : CLoops.eval env Diagonal.localTypes H (.bin .add (indexed "coeff") (indexed "coeff")) =
      some (.float64 (Binary64.addResult values[i] values[i]).encode) := by
    have unfold : CLoops.eval env Diagonal.localTypes H (.bin .add (indexed "coeff") (indexed "coeff")) =
        (CBody.eval env H (indexed "coeff")).bind
          (fun x => (CBody.eval env H (indexed "coeff")).bind (fun y => CArithmetic.floatAdd x y)) := rfl
    rw [unfold, coeffEval]
    simp only [Option.bind_some]
    exact CArithmetic.add_result _ _
  have encoded : (Binary64.addResult values[i] values[i]).encode = (Binary64.toBits result[i]).val := by
    rw [(Binary64.addResult_correct values[i] values[i] (.finite result[i])).mpr (adds i)]; rfl
  rw [encoded] at rhs
  have target : CBody.lvalue env H (.index (.id "out") (.id "offset")) =
      some (output.index (position shape i.val)) := by
    simp [henv, CBody.lvalue, CBody.lvalueWith, CBody.evalWith, CBody.resolve, CLoops.counterEnv, locals, Diagonal.parameters,
      Lowering.Arguments.locals, signatureParameters, arguments, CBody.bind, Value.address]
  have stored := scatter_store_next (zeroHeap heap output shape) output result (zero_writable heap output shape) i
  rw [← hH] at stored
  simp only [Value.finite] at stored
  change CBody.legacyExpressions.address env H (.index (.id "out") (.id "offset")) =
    some (output.index (position shape i.val)) at target
  simp only [operation, List.cons_append, List.nil_append, CLoops.next, CLoops.nextWith, rhs, target,
    stored, bind, Option.bind_some, pure]

/-- The complete diagonal loop over the zero-filled output reaches the scattered
diagonal `diag(2*u)` (`resultHeap`), then returns. -/
theorem loop_reaches (input output : Address) (result values : Values shape) (heap : Heap)
    (separate : Diagonal.Separate output input shape) (reads : Reads heap input values)
    (adds : ∀ i : Fin shape.volume, Binary64.Adds values[i] values[i] (.finite result[i]))
    (bounded : (matrixShape shape.volume shape.volume).volume < 2 ^ 64) :
    Transition.Reaches CLoops.machine.step
      (.running [CLoops.loop "k" (.id "count") operation, .ret none]
        (CLoops.counterEnv (locals input output shape 0) "k" 0) Diagonal.localTypes (zeroHeap heap output shape))
      (.returned ⟨.void, resultHeap heap output result⟩) := by
  have repeated := CLoops.loop_reaches "k" (.id "count") operation [.ret none]
    (locals input output shape) Diagonal.localTypes (scatter (zeroHeap heap output shape) output result)
    shape.volume (by simp [Diagonal.localTypes, CLoops.bindType]) (counter_bounds shape bounded).1
    (by simp [operation, CLoops.noDeclarations])
    (by
      intro i hi
      simp [CBody.eval, CBody.evalWith, CBody.resolve, CLoops.counterEnv, locals, Diagonal.parameters,
        Lowering.Arguments.locals, signatureParameters, arguments, CBody.bind])
    (by
      intro i hi
      exact .next (copy_step output input result values heap separate reads adds ⟨i, hi⟩ _)
        (.next (offset_step input output shape _ i (position_bounded shape bounded (i + 1) (by omega))
          _ (offset_eval input output shape _ bounded i hi)) (.refl _)))
  exact repeated.trans (.next rfl (.refl _))

/-- The offset/stride/counter setup before the diagonal loop, identical to the
diagonal-copy helper's; only the loop body differs. -/
theorem initialize_reaches (input output : Address) (shape : Shape) (heap : Heap)
    (bounded : (matrixShape shape.volume shape.volume).volume < 2 ^ 64)
    (sizeType : interface.types "size_t" = some .size) :
    Transition.Reaches CLoops.machine.step
      (.running tail (Diagonal.parameters input output shape) Diagonal.parameterTypes (zeroHeap heap output shape))
      (.running [CLoops.loop "k" (.id "count") operation, .ret none]
        (CLoops.counterEnv (locals input output shape 0) "k" 0) Diagonal.localTypes (zeroHeap heap output shape)) := by
  have startK := CLoops.counter_initialize (locals input output shape 0)
    (CLoops.bindType (CLoops.bindType Diagonal.parameterTypes "offset" .size) "stride" .size)
    (zeroHeap heap output shape) "k" [CLoops.loop "k" (.id "count") operation, .ret none]
    (by simp [locals, Diagonal.parameters, Lowering.Arguments.locals, signatureParameters, CBody.bind]) sizeType
  let envOffset := CLoops.counterEnv (Diagonal.parameters input output shape) "offset" 0
  let typeOffset := CLoops.bindType Diagonal.parameterTypes "offset" .size
  have evaluated := CLoops.eval_increment envOffset typeOffset (zeroHeap heap output shape) "count"
    shape.volume (by simp [envOffset, CLoops.counterEnv, Diagonal.parameters, Lowering.Arguments.locals,
      signatureParameters, arguments, CBody.bind])
    (by simp [typeOffset, Diagonal.parameterTypes, Lowering.Arguments.types, signatureParameters, CLoops.bindType,
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
    simp [envOffset, CLoops.counterEnv, Diagonal.parameters, Lowering.Arguments.locals, signatureParameters, CBody.bind]
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
  have startOffset := CLoops.counter_initialize (Diagonal.parameters input output shape) Diagonal.parameterTypes
    (zeroHeap heap output shape) "offset"
    (.declare "size_t" "stride" (.bin .add (.id "count") (.nat 1)) ::
      CLoops.counted "k" (.id "count") operation ++ [.ret none])
    (by simp [Diagonal.parameters, Lowering.Arguments.locals, signatureParameters, CBody.bind]) sizeType
  exact .next startOffset (.next startStride (.next startK (.refl _)))

/-- The helper body, from a zero-filled output, reaches `diag(2*u)` and returns. -/
theorem tail_reaches (input output : Address) (result values : Values shape) (heap : Heap)
    (separate : Diagonal.Separate output input shape) (reads : Reads heap input values)
    (adds : ∀ i : Fin shape.volume, Binary64.Adds values[i] values[i] (.finite result[i]))
    (bounded : (matrixShape shape.volume shape.volume).volume < 2 ^ 64)
    (sizeType : interface.types "size_t" = some .size) :
    Transition.Reaches CLoops.machine.step
      (.running tail (Diagonal.parameters input output shape) Diagonal.parameterTypes (zeroHeap heap output shape))
      (.returned ⟨.void, resultHeap heap output result⟩) :=
  (initialize_reaches input output shape heap bounded sizeType).trans
    (loop_reaches input output result values heap separate reads adds bounded)

/-- The complete helper body reaches `resultHeap` from any heap in which the input
is readable and the output is writable: zero-fill then the diagonal loop. -/
theorem function_reaches (definitions : CLoops.Calls.Definitions)
    (input output : Address) (result values : Values shape) (heap : Heap) (stack : CLoops.Calls.Continuation)
    (fillDefined : definitions Fill.function.signature.name = some Fill.function)
    (header : Fill.HeaderTypes interface)
    (separate : Diagonal.Separate output input shape) (reads : Reads heap input values)
    (adds : ∀ i : Fin shape.volume, Binary64.Adds values[i] values[i] (.finite result[i]))
    (writable : Writable heap output (matrixShape shape.volume shape.volume).volume)
    (bounded : (matrixShape shape.volume shape.volume).volume < 2 ^ 64) :
    Transition.Reaches (CLoops.Calls.machine definitions).step
      (.body (.running function.body (Diagonal.parameters input output shape) Diagonal.parameterTypes heap) stack)
      (.body (.returned ⟨.void, resultHeap heap output result⟩) stack) := by
  have filled := Fill.invoke_reaches definitions (matrixShape shape.volume shape.volume)
    Binary64.positiveZero output heap (CAlgorithm.literal .zero) (.id "out") (.id "cells")
    (Diagonal.parameters input output shape) Diagonal.parameterTypes tail stack fillDefined header
    (by simp [Diagonal.parameters, Lowering.Arguments.locals, signatureParameters, CBody.bind, Fill.function])
    (Fill.literal_eval .zero _ _ header.scalar)
    (by simp [CBody.eval, CBody.evalWith, CBody.resolve, Diagonal.parameters, Lowering.Arguments.locals, signatureParameters,
      arguments, CBody.bind])
    (by simp [CBody.eval, CBody.evalWith, CBody.resolve, Diagonal.parameters, Lowering.Arguments.locals, signatureParameters,
      arguments, CBody.bind]) writable bounded
  exact filled.trans (CLoops.Calls.body_reaches definitions
    (tail_reaches input output result values heap separate reads adds bounded header.size) stack)

theorem helper_call_reaches (definitions : CLoops.Calls.Definitions)
    (input output : Address) (result values : Values shape) (heap : Heap) (stack : CLoops.Calls.Continuation)
    (found : definitions function.signature.name = some function)
    (fillDefined : definitions Fill.function.signature.name = some Fill.function)
    (header : CTensor.HeaderTypes interface) (fillHeader : Fill.HeaderTypes interface)
    (separate : Diagonal.Separate output input shape) (reads : Reads heap input values)
    (adds : ∀ i : Fin shape.volume, Binary64.Adds values[i] values[i] (.finite result[i]))
    (writable : Writable heap output (matrixShape shape.volume shape.volume).volume)
    (bounded : (matrixShape shape.volume shape.volume).volume < 2 ^ 64) :
    Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling function.signature.name (Diagonal.argumentValues input output shape) heap stack)
      (.returning (resultHeap heap output result) stack) := by
  have entered : (CLoops.Calls.machine definitions).step
      (.calling function.signature.name (Diagonal.argumentValues input output shape) heap stack)
      (.body (.running function.body (Diagonal.parameters input output shape) Diagonal.parameterTypes heap) stack) := by
    simp only [CLoops.Calls.machine, CLoops.Calls.machineWith, CLoops.Calls.nextWith, found,
      show function.signature.result = "void" from rfl, ne_eq, not_true_eq_false, ↓reduceIte,
      show function.signature.parameters = Diagonal.function.signature.parameters from rfl,
      Diagonal.bind_parameters input output shape header bounded, Diagonal.bind_types header,
      bind, Option.bind_some, pure]
  exact .next entered ((function_reaches definitions input output result values heap stack fillDefined fillHeader
    separate reads adds writable bounded).trans (.next
      (by simp [CLoops.Calls.machine, CLoops.Calls.machineWith, CLoops.Calls.nextWith]) (.refl _)))

/-- Correctness of the ordinary call: the sole terminating behavior writes the
dense diagonal matrix `diag(2*u)` into the output region (`resultHeap`). -/
theorem helper_call_correct (definitions : CLoops.Calls.Definitions)
    (input output : Address) (result values : Values shape) (heap : Heap)
    (found : definitions function.signature.name = some function)
    (fillDefined : definitions Fill.function.signature.name = some Fill.function)
    (header : CTensor.HeaderTypes interface) (fillHeader : Fill.HeaderTypes interface)
    (separate : Diagonal.Separate output input shape) (reads : Reads heap input values)
    (adds : ∀ i : Fin shape.volume, Binary64.Adds values[i] values[i] (.finite result[i]))
    (writable : Writable heap output (matrixShape shape.volume shape.volume).volume)
    (bounded : (matrixShape shape.volume shape.volume).volume < 2 ^ 64) (behavior) :
    (CLoops.Calls.machine definitions).Behaves
      (.calling function.signature.name (Diagonal.argumentValues input output shape) heap .done) behavior ↔
      behavior = .terminates (resultHeap heap output result) := by
  have ran := helper_call_reaches definitions input output result values heap .done found fillDefined header
    fillHeader separate reads adds writable bounded
  exact (CLoops.Calls.machine definitions).behavior_iff (ran.trans (.next rfl (.refl _))) rfl

/-- Inlining the call at a body site: from a running body with the four argument
expressions evaluating to the input/output pointers and the two counts, one step
advances past the call with the output region holding `diag(2*u)`. -/
theorem invoke_reaches (definitions : CLoops.Calls.Definitions)
    (input output : Address) (result values : Values shape) (heap : Heap)
    (argInput argOutput argCount argCells : Expr) (env : CBody.Locals) (types : CLoops.Types)
    (rest : List Stmt) (stack : CLoops.Calls.Continuation)
    (found : definitions function.signature.name = some function)
    (fillDefined : definitions Fill.function.signature.name = some Fill.function)
    (header : CTensor.HeaderTypes interface) (fillHeader : Fill.HeaderTypes interface)
    (unshadowed : env function.signature.name = none)
    (hc : CBody.eval env heap argInput = some (.pointer (some input)))
    (ho : CBody.eval env heap argOutput = some (.pointer (some output)))
    (hn : CBody.eval env heap argCount = some (.integer shape.volume))
    (ha : CBody.eval env heap argCells = some (.integer (matrixShape shape.volume shape.volume).volume))
    (separate : Diagonal.Separate output input shape) (reads : Reads heap input values)
    (adds : ∀ i : Fin shape.volume, Binary64.Adds values[i] values[i] (.finite result[i]))
    (writable : Writable heap output (matrixShape shape.volume shape.volume).volume)
    (bounded : (matrixShape shape.volume shape.volume).volume < 2 ^ 64) :
    Transition.Reaches (CLoops.Calls.machine definitions).step
      (.body (.running (invoke argInput argOutput argCount argCells :: rest) env types heap) stack)
      (.body (.running rest env types (resultHeap heap output result)) stack) := by
  have started : CLoops.Calls.next definitions
      (.body (.running (invoke argInput argOutput argCount argCells :: rest) env types heap) stack) =
      some (.calling function.signature.name (Diagonal.argumentValues input output shape) heap
        (.caller rest env types stack)) := by
    simp only [function] at unshadowed
    simp [invoke, function, CLoops.Calls.next, CLoops.Calls.nextWith, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith,
      CLoops.Calls.enterCallWith, CCalls.argumentsWith, CBody.legacyExpressions, hc, ho, hn, ha, Diagonal.argumentValues, unshadowed]
  exact .next started ((helper_call_reaches definitions input output result values heap _ found fillDefined
    header fillHeader separate reads adds writable bounded).trans (.next rfl (.refl _)))

omit interface in
/-- After the call, the output region reads the dense diagonal matrix `diag(2*u)`. -/
theorem output_reads (heap : Heap) (output : Address) (result : Values shape) :
    Reads (resultHeap heap output result) output (matrix result) :=
  result_reads heap output result

omit interface in
/-- Every cell outside the output matrix region is preserved. -/
theorem output_frame (heap : Heap) (output : Address) (result : Values shape) (q : Address)
    (outside : ∀ i < (matrixShape shape.volume shape.volume).volume, q ≠ output.index i) :
    resultHeap heap output result q = heap q :=
  result_frame heap output result q outside

/-! ### Relation to the prepared AD Jacobian program

Each written diagonal entry `u[k] + u[k]` is a nearest finite value to
`2 * value u[k]`, which is exactly the `(k, k)` entry of the real Jacobian
`AD.squareJacobian` produced by `ArrayProfile.squareJacobianProgram`
(`square_jacobian_eval`). No `2 * u` simplification is inserted: the two ordered
additions are retained, and only their nearest-value property is asserted. -/
omit interface in
theorem diagonal_nearest (values : Values shape)
    (result : Values shape)
    (adds : ∀ i : Fin shape.volume, Binary64.Adds values[i] values[i] (.finite result[i]))
    (i : Fin shape.volume) (candidate : Binary64.Value) :
    |Binary64.value result[i] - 2 * Binary64.value values[i]| ≤
      |Binary64.value candidate - 2 * Binary64.value values[i]| := by
  have finite : result[i] = Binary64.roundedAdd values[i] values[i] :=
    Binary64.sum_rounding_unique (adds i).2.2 (Binary64.roundedAdd_spec values[i] values[i])
  rw [finite]
  simpa only [two_mul] using Binary64.roundedAdd_nearest values[i] values[i] candidate

omit interface in
/-- The written diagonal matrix equals the dense diagonal of the real Jacobian's
`(k,k)` entries at their nearest finite values. This ties the materialized output
to `AD.squareJacobian` through `square_jacobian_eval`: the real Jacobian of
`der(x) = u .* u` is `Matrix.diagonal (fun i => u i + u i)`. -/
theorem matrix_diagonal_nearest (result : Values shape) (i j : Fin shape.volume) :
    (matrix result)[Rumoca.Tensor.matrixIndex (i, j)] =
      if i = j then result[i] else Binary64.positiveZero :=
  Diagonal.matrix_get result i j

end Rumoca.CTensor.SquareDiagonal
