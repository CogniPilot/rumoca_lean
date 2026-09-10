import RumocaC.TensorCode
import RumocaC.TensorMemory
import RumocaC.LoopProofs
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

theorem index_eval (env : CBody.Locals) (heap : Heap) (name : String) (base : Address) (i : Nat)
    (pointer : env name = some (.pointer (some base))) (counter : env "k" = some (.integer i)) :
    CBody.eval env heap (indexed name) = load heap (base.index i) := by
  simp [indexed, CBody.eval, CBody.resolve, pointer, counter, Value.address]

theorem index_lvalue (env : CBody.Locals) (heap : Heap) (name : String) (base : Address) (i : Nat)
    (pointer : env name = some (.pointer (some base))) (counter : env "k" = some (.integer i)) :
    CBody.lvalue env heap (indexed name) = some (base.index i) := by
  simp [indexed, CBody.lvalue, CBody.eval, CBody.resolve, pointer, counter, Value.address]

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

private theorem operation_step (op : Tensor.BinaryOp) (a b : Values shape)
    (heap : Heap) (left right output : Address) (i : Fin shape.volume) (rest : List Stmt)
    (read_left : Reads heap left a) (read_right : Reads heap right b)
    (write_output : Writable heap output shape.volume)
    (separate_left : Separate output left shape.volume) (separate_right : Separate output right shape.volume)
    (domain : Finite.Domain op a[i] b[i]) :
    CLoops.next (.running (operation op ++ rest)
      (CLoops.counterEnv (parameters left right output shape.volume) "k" i.val) localTypes
      (written heap output (op.eval Finite.ops a b) i.val)) =
      some (.running rest (CLoops.counterEnv (parameters left right output shape.volume) "k" i.val)
        localTypes (written heap output (op.eval Finite.ops a b) (i.val + 1))) := by
  let env := CLoops.counterEnv (parameters left right output shape.volume) "k" i.val
  let before := written heap output (op.eval Finite.ops a b) i.val
  have hk : env "k" = some (.integer i.val) := by simp [env, CLoops.counterEnv, CBody.bind]
  have hl := index_eval env before "left" left i.val
    (by simp [env, CLoops.counterEnv, CBody.bind, parameters]) hk
  have hr := index_eval env before "right" right i.val
    (by simp [env, CLoops.counterEnv, CBody.bind, parameters]) hk
  have ho := index_lvalue env before "out" output i.val
    (by simp [env, CLoops.counterEnv, CBody.bind, parameters]) hk
  have ha := reads_written heap output left (op.eval Finite.ops a b) a i.val separate_left read_left i
  have hb := reads_written heap output right (op.eval Finite.ops a b) b i.val separate_right read_right i
  have he := operation_eval op env before a[i] b[i] (hl.trans ha) (hr.trans hb) domain
  have hs := store_next heap output (op.eval Finite.ops a b) write_output i.val i.isLt
  have hv : (op.eval Finite.ops a b)[i] = op.scalar Finite.ops a[i] b[i] :=
    op.eval_correct Finite.ops a b i
  rw [← Fin.getElem_fin, hv] at hs
  change store before (output.index i.val) (.finite (op.scalar Finite.ops a[i] b[i])) = _ at hs
  change CLoops.next (.running (operation op ++ rest) env localTypes before) = _
  simp only [indexed] at he ho
  simp only [operation, indexed, List.singleton_append, CLoops.next, he, ho, hs,
    bind, Option.bind_some, pure]
  rfl

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
  have repeated := CLoops.loop_reaches "k" (.id "count") (operation op) [.ret none]
    (fun _ => parameters left right output shape.volume) localTypes
    (written heap output (op.eval Finite.ops a b)) shape.volume
    (by simp [localTypes, CLoops.bindType]) bounded
    (by simp [operation, CLoops.noDeclarations])
    (by intro i _; simp [CBody.eval, CBody.resolve, CLoops.counterEnv, CBody.bind, parameters])
    (by
      intro i hi
      exact .next (operation_step op a b heap left right output ⟨i, hi⟩ _ read_left read_right
        write_output separate_left separate_right (domain ⟨i, hi⟩)) (.refl _))
  have started := CLoops.counter_initialize (parameters left right output shape.volume) parameterTypes heap "k"
    [CLoops.loop "k" (.id "count") (operation op), .ret none]
    (by simp [parameters]) size_type
  have reaches : Transition.Reaches CLoops.machine.step
      (.running (function op).body (parameters left right output shape.volume) parameterTypes heap)
      (.returned ⟨.void, written heap output (op.eval Finite.ops a b) shape.volume⟩) :=
    .next started (repeated.trans (.next (by rfl) (.refl _)))
  exact CLoops.machine.behavior_iff reaches rfl

omit interface in
theorem output_correct (op : Tensor.BinaryOp) (a b : Values shape) (heap : Heap) (output : Address) :
    Reads (written heap output (op.eval Finite.ops a b) shape.volume) output (op.eval Finite.ops a b) :=
  written_reads _ _ _

end Rumoca.CTensor
