import RumocaC.TensorCode
import RumocaC.TensorMemory
import RumocaC.LoopProofs

/-! Shared proof for a counted buffer writer. Clients must prove the actual
C expression reads/evaluates to each specified value in the current heap.
This theorem then executes every typed store, counter step and return. -/
noncomputable section
namespace Rumoca.CTensor
open CTree CMemory CMemory.TensorView
variable [interface : CInterface]

theorem index_eval (env : CBody.Locals) (heap : Heap) (name : String) (base : Address) (i : Nat)
    (pointer : env name = some (.pointer (some base))) (counter : env "k" = some (.integer i)) :
    CBody.eval env heap (indexed name) = load heap (base.index i) := by
  simp [indexed, CBody.eval, CBody.evalWith, CBody.resolve, pointer, counter, Value.address]

theorem index_lvalue (env : CBody.Locals) (heap : Heap) (name : String) (base : Address) (i : Nat)
    (pointer : env name = some (.pointer (some base))) (counter : env "k" = some (.integer i)) :
    CBody.lvalue env heap (indexed name) = some (base.index i) := by
  simp [indexed, CBody.lvalue, CBody.lvalueWith, CBody.evalWith, CBody.resolve, pointer, counter, Value.address]

theorem write_step (expr : Expr) (values : Values shape) (env : CBody.Locals) (types : CLoops.Types)
    (heap : Heap) (output : Address) (i : Fin shape.volume) (rest : List Stmt)
    (pointer : env "out" = some (.pointer (some output)))
    (counter : env "k" = some (.integer i.val)) (writable : Writable heap output shape.volume)
    (evaluated : CLoops.eval env types (written heap output values i.val) expr = some (.finite values[i])) :
    CLoops.next (.running (.assign (indexed "out") expr :: rest) env types
      (written heap output values i.val)) =
      some (.running rest env types (written heap output values (i.val + 1))) := by
  have target := index_lvalue env (written heap output values i.val) "out" output i.val pointer counter
  have stored := store_next heap output values writable i.val i.isLt
  rw [← Fin.getElem_fin] at stored
  simp only [indexed] at target ⊢
  change CBody.legacyExpressions.address env (written heap output values i.val)
    (Expr.index (.id "out") (.id "k")) = some (output.index i.val) at target
  simp only [CLoops.next, CLoops.nextWith, evaluated, target, stored, bind, Option.bind_some, pure]

theorem writer_reaches (expr : Expr) (values : Values shape) (env : CBody.Locals) (types : CLoops.Types)
    (heap : Heap) (output : Address) (pointer : env "out" = some (.pointer (some output)))
    (count : env "count" = some (.integer shape.volume)) (fresh : env "k" = none)
    (writable : Writable heap output shape.volume) (bounded : shape.volume < 2 ^ 64)
    (size_type : interface.types "size_t" = some .size)
    (evaluated : ∀ i : Fin shape.volume,
      CLoops.eval (CLoops.counterEnv env "k" i.val) (CLoops.bindType types "k" .size)
        (written heap output values i.val) expr = some (.finite values[i])) :
    Transition.Reaches CLoops.machine.step
      (.running (CLoops.counted "k" (.id "count") [.assign (indexed "out") expr] ++ [.ret none])
        env types heap)
      (.returned ⟨.void, written heap output values shape.volume⟩) := by
  have repeated := CLoops.loop_reaches "k" (.id "count") [.assign (indexed "out") expr] [.ret none]
    (fun _ => env) (CLoops.bindType types "k" .size) (written heap output values) shape.volume
    (by simp [CLoops.bindType]) bounded (by simp [CLoops.noDeclarations])
    (by intro i _; simp [CBody.eval, CBody.evalWith, CBody.resolve, CLoops.counterEnv, CBody.bind, count])
    (by
      intro i hi
      exact .next (write_step expr values _ _ heap output ⟨i, hi⟩ _
        (by simp [CLoops.counterEnv, CBody.bind, pointer])
        (by simp [CLoops.counterEnv, CBody.bind]) writable (evaluated ⟨i, hi⟩)) (.refl _))
  have started := CLoops.counter_initialize env types heap "k"
    [CLoops.loop "k" (.id "count") [.assign (indexed "out") expr], .ret none] fresh size_type
  exact .next started (repeated.trans (.next rfl (.refl _)))

end Rumoca.CTensor
