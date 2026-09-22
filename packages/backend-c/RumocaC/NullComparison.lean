import RumocaC.Body

/-! Pointer comparisons with a null pointer, corresponding to C11
6.3.2.3p3–4 and 6.5.9p6. This does not assign native addresses to symbolic
subobjects or decide equality between two non-null pointers. The latter needs
object/layout information; relational pointer comparisons remain unsupported.
The null operand must already be typed as a pointer. Evaluating an arbitrary
integer variable to zero does not make it a C null pointer constant. -/
namespace Rumoca.CNull
open CTree CMemory CBody

/-- Independent equality/inequality judgment on the supported null domain. -/
inductive Compared : BinOp → Option Address → Option Address → Bool → Prop where
  | equal (null : a = none ∨ b = none) (value : result = true ↔ a = b) :
      Compared .eq a b result
  | unequal (null : a = none ∨ b = none) (value : result = true ↔ a ≠ b) :
      Compared .ne a b result

theorem Compared.iff : Compared op a b result ↔
    (a = none ∨ b = none) ∧
      ((op = .eq ∧ (result = true ↔ a = b)) ∨
       (op = .ne ∧ (result = true ↔ a ≠ b))) := by
  constructor
  · intro h
    cases h with
    | equal null value => exact ⟨null, Or.inl ⟨rfl, value⟩⟩
    | unequal null value => exact ⟨null, Or.inr ⟨rfl, value⟩⟩
  · rintro ⟨null, ⟨rfl, value⟩ | ⟨rfl, value⟩⟩
    · exact .equal null value
    · exact .unequal null value

theorem comparison_iff (op : BinOp) (a b : Option Address) (result : Bool) :
    comparison op (.pointer a) (.pointer b) = some (boolean result) ↔
      Compared op a b result := by
  rw [Compared.iff]
  cases op <;> cases a <;> cases b <;> cases result <;> simp [comparison, boolean]

@[simp] theorem equal_right (p : Option Address) :
    comparison .eq (.pointer p) (.pointer none) = some (boolean p.isNone) := by
  cases p <;> rfl

@[simp] theorem unequal_right (p : Option Address) :
    comparison .ne (.pointer p) (.pointer none) = some (boolean p.isSome) := by
  cases p <;> rfl

@[simp] theorem equal_left (p : Option Address) :
    comparison .eq (.pointer none) (.pointer p) = some (boolean p.isNone) := by
  cases p <;> rfl

@[simp] theorem unequal_left (p : Option Address) :
    comparison .ne (.pointer none) (.pointer p) = some (boolean p.isSome) := by
  cases p <;> rfl

theorem nonnull_unsupported (op : BinOp) (a b : Address) :
    comparison op (.pointer (some a)) (.pointer (some b)) = none := by
  cases op <;> rfl

variable [interface : CInterface]

@[simp] theorem literal_eval (type : interface.types "void *" = some .pointer)
    (env : Locals) (heap : Heap) :
    eval env heap Expr.nullPointer = some (.pointer none) := by
  simp [Expr.nullPointer, eval, expressionCast, zeroLiteral, type]

theorem zero_variable_not_constant (name : String) (type : interface.types spelling = some .pointer) :
    expressionCast spelling (.id name) (.integer 0) = none := by
  simp [expressionCast, zeroLiteral, CBody.cast, type, convert]

theorem equal_eval (pointer null : Expr) (env : Locals) (heap : Heap) (p : Option Address)
    (hp : eval env heap pointer = some (.pointer p))
    (hn : eval env heap null = some (.pointer none)) :
    eval env heap (.bin .eq pointer null) = eval env heap (.not pointer) := by
  cases p <;> simp [eval, hp, hn, Value.truth, comparison]

theorem unequal_truth (pointer null : Expr) (env : Locals) (heap : Heap) (p : Option Address)
    (hp : eval env heap pointer = some (.pointer p))
    (hn : eval env heap null = some (.pointer none)) :
    (eval env heap (.bin .ne pointer null) >>= Value.truth) =
      (eval env heap pointer >>= Value.truth) := by
  cases p <;> simp [eval, hp, hn, Value.truth, comparison, boolean]

theorem branch_preserved (pointer : Expr) (env : Locals) (heap : Heap) (p : Option Address)
    (hp : eval env heap pointer = some (.pointer p))
    (type : interface.types "void *" = some .pointer) (yes no rest : List Stmt) :
    next (.running (.branch (.bin .eq pointer Expr.nullPointer) yes no :: rest) env heap) =
      next (.running (.branch (.not pointer) yes no :: rest) env heap) := by
  simp only [next, equal_eval pointer Expr.nullPointer env heap p hp (literal_eval type env heap)]

/-- An explicit null comparison preserves lazy conjunction even when the
right operand has no evaluation result. -/
theorem and_unequal_null_eval (pointer right : Expr) (env : Locals) (heap : Heap)
    (p : Option Address)
    (hp : eval env heap pointer = some (.pointer p))
    (type : interface.types "void *" = some .pointer) :
    eval env heap (.bin .and (.bin .ne pointer Expr.nullPointer) right) =
      eval env heap (.bin .and pointer right) := by
  have truth := unequal_truth pointer Expr.nullPointer env heap p hp (literal_eval type env heap)
  cases p <;> simp_all [eval, literal_eval type env heap, Value.truth, comparison]

/-- An explicit null comparison likewise preserves lazy disjunction. -/
theorem or_unequal_null_eval (pointer right : Expr) (env : Locals) (heap : Heap)
    (p : Option Address)
    (hp : eval env heap pointer = some (.pointer p))
    (type : interface.types "void *" = some .pointer) :
    eval env heap (.bin .or (.bin .ne pointer Expr.nullPointer) right) =
      eval env heap (.bin .or pointer right) := by
  have truth := unequal_truth pointer Expr.nullPointer env heap p hp (literal_eval type env heap)
  cases p <;> simp_all [eval, literal_eval type env heap, Value.truth, comparison]

/-- A null left pointer makes conjunction false without evaluating the right. -/
theorem and_unequal_null_short_circuit (pointer right : Expr) (env : Locals) (heap : Heap)
    (hp : eval env heap pointer = some (.pointer none))
    (type : interface.types "void *" = some .pointer) :
    eval env heap (.bin .and (.bin .ne pointer Expr.nullPointer) right) =
      some (boolean false) := by
  rw [and_unequal_null_eval pointer right env heap none hp type]
  simp [eval, hp, Value.truth]

end Rumoca.CNull
