import RumocaC.InitializationCode
import RumocaC.Body
import RumocaC.TreeLexical

/-! Explicit initialization writes from the prepared Solve plan. This module
does not select an initial value or inspect Modelica declarations. Allocation,
scope entry and the enclosing adapter's complete file contract are separate. -/
namespace Rumoca.CInitialization
open CTree CMemory

theorem value_zero (model : Solve.Model source) : value model = .cast "double" (.nat 0) := by
  rw [value, model.initial_default]

/-- Independent token spelling of the emitted double constant. -/
theorem value_printed (model : Solve.Model source) :
    _root_.Parser.Scanner.Lexes CTree.Syntax.config (value model).render.toList
      ((["(", "(", "double", ")", "0", ")"] : List String).map _root_.Parser.Token.literal) := by
  rw [value_zero]
  have printed : (Expr.cast "double" (.nat 0)).render = "((double)0)" := by
    simp [Expr.render, Nat.repr_eq_ofList_toDigits, Nat.toDigits_zero]
  rw [printed]
  c_lex_fixed

variable [interface : CInterface]

theorem value_evaluated (model : Solve.Model source) (env : CBody.Locals) (heap : Heap)
    (double : interface.types "double" = some .float64) :
    CBody.eval env heap (value model) = some (.finite Binary64.positiveZero) := by
  rw [value_zero]
  simp [CBody.eval, CBody.evalWith, CBody.cast, double, convert]

def written (heap : Heap) (address : Address) : Heap :=
  replace heap address ⟨.float64, true, some (.finite Binary64.positiveZero)⟩

/-- The write initializes a valid writable cell even when its previous value
is absent or arbitrary; it does not rely on zero-filled allocation. -/
theorem write_step (model : Solve.Model source) (target : Expr)
    (env : CBody.Locals) (heap : Heap) (address : Address) (old : Option Value)
    (double : interface.types "double" = some .float64)
    (located : CBody.lvalue env heap target = some address)
    (storage : heap address = some ⟨.float64, true, old⟩) (rest : List Stmt) :
    CBody.next (.running ((emit model target).statement :: rest) env heap) =
      some (.running rest env (written heap address)) := by
  simp [CBody.next, CBody.nextWith, CBody.legacyExpressions, Emission.statement, value_evaluated model env heap double, located,
    store_float64 heap address old (Binary64.toBits Binary64.positiveZero).val storage,
    Value.finite, written]

omit interface in
theorem written_frame (heap : Heap) (address other : Address) (different : other ≠ address) :
    written heap address other = heap other := by
  simp [written, replace, different]

theorem write_behaviors (model : Solve.Model source) (target : Expr)
    (env : CBody.Locals) (heap : Heap) (address : Address) (old : Option Value)
    (double : interface.types "double" = some .float64)
    (located : CBody.lvalue env heap target = some address)
    (storage : heap address = some ⟨.float64, true, old⟩) (behavior) :
    CBody.machine.Behaves
      (.running [(emit model target).statement, .ret none] env heap) behavior ↔
      behavior = .terminates ⟨.void, written heap address⟩ := by
  apply CBody.behaviors_of_run (n := 2)
  rw [CBody.run, write_step model target env heap address old double located storage]
  rfl

end Rumoca.CInitialization
