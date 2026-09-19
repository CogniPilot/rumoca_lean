import RumocaC.TensorWriter
import RumocaCore.Solve.Tensor.Finite

/-! Pointwise C loops implement the finite Solve operator on all coordinates.
The theorem executes the actual mutable loop and preserves the full heap
outside its output range. Inputs may alias one another. Native ABI binding,
overflow/error paths and whole-program scratch allocation are later edges. -/
noncomputable section
namespace Rumoca.CTensor
open CTree CMemory CMemory.TensorView
open Solve.Tensor
variable [interface : CInterface]
set_option maxRecDepth 10000

def parameters (left right output : Address) (count : Nat) : CBody.Locals := fun name =>
  if name = "left" then some (.pointer (some left))
  else if name = "right" then some (.pointer (some right))
  else if name = "out" then some (.pointer (some output))
  else if name = "count" then some (.integer count)
  else none

def parameterTypes : CLoops.Types := fun name =>
  if name = "count" then some .size
  else if name = "left" ∨ name = "right" ∨ name = "out" then some .pointer else none

def localTypes : CLoops.Types := CLoops.bindType parameterTypes "k" .size

theorem operation_eval (op : Tensor.BinaryOp) (env : CBody.Locals) (heap : Heap)
    (a b : Binary64.Value) (left : CBody.eval env heap (indexed "left") = some (.finite a))
    (right : CBody.eval env heap (indexed "right") = some (.finite b)) (domain : Finite.Domain op a b) :
    CLoops.eval env localTypes heap (.bin (binaryOp op) (indexed "left") (indexed "right")) =
      some (.finite (op.scalar Finite.ops a b)) := by
  simp only [indexed] at left right
  cases op with
  | add =>
    simpa only [binaryOp, indexed, CLoops.eval, left, right, bind, Option.bind_some,
      Tensor.BinaryOp.scalar, Finite.ops] using CArithmetic.floatAdd_finite a b domain
  | mul =>
    simpa only [binaryOp, indexed, CLoops.eval, left, right, bind, Option.bind_some,
      Tensor.BinaryOp.scalar, Finite.ops] using CArithmetic.floatMul_finite a b domain
  | sub =>
    simpa only [binaryOp, indexed, CLoops.eval, left, right, bind, Option.bind_some,
      Tensor.BinaryOp.scalar, Finite.ops] using CArithmetic.floatSub_finite a b domain
  | div =>
    simpa only [binaryOp, indexed, CLoops.eval, left, right, bind, Option.bind_some,
      Tensor.BinaryOp.scalar, Finite.ops] using CArithmetic.floatDiv_finite a b domain

private theorem operation_eval_written (op : Tensor.BinaryOp) (a b : Values shape)
    (heap : Heap) (left right output : Address) (i : Fin shape.volume)
    (read_left : Reads heap left a) (read_right : Reads heap right b)
    (separate_left : Separate output left shape.volume) (separate_right : Separate output right shape.volume)
    (domain : Finite.Domain op a[i] b[i]) :
    CLoops.eval (CLoops.counterEnv (parameters left right output shape.volume) "k" i.val) localTypes
      (written heap output (op.eval Finite.ops a b) i.val)
      (.bin (binaryOp op) (indexed "left") (indexed "right")) =
      some (.finite (op.eval Finite.ops a b)[i]) := by
  let env := CLoops.counterEnv (parameters left right output shape.volume) "k" i.val
  let before := written heap output (op.eval Finite.ops a b) i.val
  have hk : env "k" = some (.integer i.val) := by simp [env, CLoops.counterEnv, CBody.bind]
  have hl := index_eval env before "left" left i.val
    (by simp [env, CLoops.counterEnv, CBody.bind, parameters]) hk
  have hr := index_eval env before "right" right i.val
    (by simp [env, CLoops.counterEnv, CBody.bind, parameters]) hk
  have ha := reads_written heap output left (op.eval Finite.ops a b) a i.val separate_left read_left i
  have hb := reads_written heap output right (op.eval Finite.ops a b) b i.val separate_right read_right i
  rw [op.eval_correct]
  exact operation_eval op env before a[i] b[i] (hl.trans ha) (hr.trans hb) domain

theorem function_reaches (op : Tensor.BinaryOp) (a b : Values shape)
    (heap : Heap) (left right output : Address)
    (read_left : Reads heap left a) (read_right : Reads heap right b)
    (write_output : Writable heap output shape.volume)
    (separate_left : Separate output left shape.volume) (separate_right : Separate output right shape.volume)
    (domain : ∀ i : Fin shape.volume, Finite.Domain op a[i] b[i]) (bounded : shape.volume < 2 ^ 64)
    (size_type : interface.types "size_t" = some .size) :
    Transition.Reaches CLoops.machine.step
      (.running (function op).body (parameters left right output shape.volume) parameterTypes heap)
      (.returned ⟨.void, written heap output (op.eval Finite.ops a b) shape.volume⟩) := by
  exact writer_reaches (.bin (binaryOp op) (indexed "left") (indexed "right"))
    (op.eval Finite.ops a b) (parameters left right output shape.volume) parameterTypes heap output
    (by simp [parameters]) (by simp [parameters]) (by simp [parameters]) write_output bounded size_type
    (fun i => operation_eval_written op a b heap left right output i read_left read_right
      separate_left separate_right (domain i))

/-- All behaviors of the actual generated loop body terminate with the
finite Solve result in the output buffer. No divergence or stuck execution
is possible under these input, storage and arithmetic premises. -/
theorem function_correct (op : Tensor.BinaryOp) (a b : Values shape)
    (heap : Heap) (left right output : Address)
    (read_left : Reads heap left a) (read_right : Reads heap right b)
    (write_output : Writable heap output shape.volume)
    (separate_left : Separate output left shape.volume) (separate_right : Separate output right shape.volume)
    (domain : ∀ i : Fin shape.volume, Finite.Domain op a[i] b[i]) (bounded : shape.volume < 2 ^ 64)
    (size_type : interface.types "size_t" = some .size) (behavior) :
    CLoops.machine.Behaves
      (.running (function op).body (parameters left right output shape.volume) parameterTypes heap) behavior ↔
      behavior = .terminates ⟨.void, written heap output (op.eval Finite.ops a b) shape.volume⟩ := by
  exact CLoops.machine.behavior_iff (function_reaches op a b heap left right output read_left read_right
    write_output separate_left separate_right domain bounded size_type) rfl

omit interface in
theorem output_correct (op : Tensor.BinaryOp) (a b : Values shape) (heap : Heap) (output : Address) :
    Reads (written heap output (op.eval Finite.ops a b) shape.volume) output (op.eval Finite.ops a b) :=
  written_reads _ _ _

end Rumoca.CTensor
