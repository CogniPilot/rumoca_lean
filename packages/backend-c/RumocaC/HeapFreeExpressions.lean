import RumocaC.Loops

/-! Conservative syntax certificates for expressions whose values or lvalue
addresses depend on locals and constant bindings, but not on object memory.
Memory-reading expressions and calls are left to region-dependent rules. -/
namespace Rumoca.CBody.Footprint
open CTree CMemory

mutual
  def heapFreeValue : Expr → Bool
    | .id _ | .nat _ | .str _ => true
    | .cast _ value | .not value => heapFreeValue value
    | .bin _ left right => heapFreeValue left && heapFreeValue right
    | .address target => heapFreeAddress target
    | _ => false

  def heapFreeAddress : Expr → Bool
    | .deref pointer => heapFreeValue pointer
    | .field base _ pointer => if pointer then heapFreeValue base else heapFreeAddress base
    | .index base index => heapFreeValue base && heapFreeValue index
    | _ => false
end

variable [CInterface]

/-- The certificate is sound for all environments and heaps, including
failure: interference cannot turn a certified expression into another result. -/
theorem heap_free (expr : Expr) :
    (heapFreeValue expr = true → ∀ env before after, eval env before expr = eval env after expr) ∧
    (heapFreeAddress expr = true → ∀ env before after, lvalue env before expr = lvalue env after expr) := by
  cases expr with
  | id | nat | str => constructor <;> simp [heapFreeValue, heapFreeAddress, eval, lvalue]
  | cast type value =>
    constructor
    · intro accepted env before after
      simp only [eval, (heap_free value).1 accepted env before after]
    · simp [heapFreeAddress]
  | not value =>
    constructor
    · intro accepted env before after
      simp only [eval, (heap_free value).1 accepted env before after]
    · simp [heapFreeAddress]
  | bin op left right =>
    constructor
    · intro accepted env before after
      obtain ⟨l, r⟩ := Bool.and_eq_true_iff.mp accepted
      have leftEq := (heap_free left).1 l env before after
      have rightEq := (heap_free right).1 r env before after
      cases op <;> simp only [eval, leftEq, rightEq]
    · simp [heapFreeAddress]
  | address target =>
    constructor
    · intro accepted env before after
      simp only [eval, (heap_free target).2 accepted env before after]
    · simp [heapFreeAddress]
  | deref pointer =>
    constructor
    · simp [heapFreeValue]
    · intro accepted env before after
      simp only [lvalue, (heap_free pointer).1 accepted env before after]
  | field base name pointer =>
    constructor
    · simp [heapFreeValue]
    · intro accepted env before after
      cases pointer with
      | true => simp only [lvalue, ↓reduceIte, (heap_free base).1 accepted env before after]
      | false => simp only [lvalue, Bool.false_eq_true, ↓reduceIte, (heap_free base).2 accepted env before after]
  | index base index =>
    constructor
    · simp [heapFreeValue]
    · intro accepted env before after
      obtain ⟨b, i⟩ := Bool.and_eq_true_iff.mp accepted
      -- A base certified `heapFreeValue` is not an lvalue expression, so the
      -- array-decay fallback branch is unreachable and heap-independent.
      have lvNone : ∀ h, lvalue env h base = none := by
        cases base <;> simp_all [heapFreeValue, lvalue]
      simp only [lvalue, (heap_free base).1 b env before after, (heap_free index).1 i env before after,
        lvNone]
  | call | decimal | sizeof => simp [heapFreeValue, heapFreeAddress]
termination_by sizeOf expr

end Rumoca.CBody.Footprint

namespace Rumoca.CBody.Footprint
open CTree CMemory
variable [CInterface]

/-- The same certificate covers the typed loop evaluator, including its
unsigned-counter and floating arithmetic rules. -/
theorem loop_heap_free (accepted : heapFreeValue expr = true)
    (env : CBody.Locals) (types : CLoops.Types) (before after : Heap) :
    CLoops.eval env types before expr = CLoops.eval env types after expr := by
  have support : ∀ value, heapFreeValue value = true →
      CBody.eval env before value = CBody.eval env after value :=
    fun value valid => (heap_free value).1 valid env before after
  unfold CLoops.eval
  split <;> simp_all only [heapFreeValue, Bool.and_eq_true]

end Rumoca.CBody.Footprint
