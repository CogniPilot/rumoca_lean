import RumocaC.Body

/-! The exact integer and finite Float64 casts used by the authored C subset.
Integer encodings agree with mathematical values; floating-to-size casts use
C11 6.3.1.4 truncation and representability, with no modulo on floating inputs.
Native layout, floating flags/traps and later machine compilation remain
outside these symbolic object and expression semantics. -/
namespace Rumoca.CIntegerConversions
open CTree CMemory

theorem integer_float64 (n : Int) (small : n.natAbs < 2 ^ 53) :
    convert .float64 (.integer n) = some (.finite (Binary64.ofSmallInt n small)) := by
  simp only [convert, Binary64.exactInteger?, dif_pos small, Option.map_some]

theorem integer_float64_value (converted : convert .float64 (.integer n) = some result) :
    ∃ value, result = .finite value ∧ Binary64.value value = (n : ℝ) := by
  change (Binary64.exactInteger? n).map Value.finite = some result at converted
  obtain ⟨value, accepted, same⟩ := Option.map_eq_some_iff.mp converted
  exact ⟨value, same.symm, Binary64.exactInteger_sound accepted⟩

theorem finite_size (x : Binary64.Value)
    (bounded : 0 ≤ Binary64.truncateInteger x ∧ Binary64.truncateInteger x < 2 ^ 64) :
    convert .size (.finite x) = some (.integer (Binary64.truncateInteger x)) := by
  simp only [convert, Value.finite, Float64.decode_finite, if_pos bounded]

theorem finite_size_iff (x : Binary64.Value) (n : Int) :
    convert .size (.finite x) = some (.integer n) ↔
      n = Binary64.truncateInteger x ∧ 0 ≤ n ∧ n < 2 ^ 64 := by
  simp only [convert, Value.finite, Float64.decode_finite]
  split <;> simp_all [eq_comm]

theorem nonfinite_size (bits : BitVec 64)
    (nonfinite : ∀ value, Float64.decode bits ≠ .finite value) :
    convert .size (.float64 bits) = none := by
  cases decoded : Float64.decode bits with
  | finite value => exact False.elim (nonfinite value decoded)
  | negativeInfinity | positiveInfinity | nan => simp only [convert, decoded]

/-- The returned integer has the standard's mathematical truncation value
and fits the selected unsigned 64-bit profile. -/
theorem finite_size_correct (x : Binary64.Value) (n : Int)
    (converted : convert .size (.finite x) = some (.integer n)) :
    n = (if 0 ≤ Binary64.value x then ⌊Binary64.value x⌋ else ⌈Binary64.value x⌉) ∧
      0 ≤ n ∧ n < 2 ^ 64 := by
  obtain ⟨same, bounded⟩ := (finite_size_iff x n).mp converted
  exact ⟨same.trans (Binary64.truncateInteger_correct x), bounded⟩

variable [interface : CInterface]

theorem cast_integer (type : String) (n : Int)
    (declared : interface.types type = some .float64) (small : n.natAbs < 2 ^ 53) :
    CBody.cast type (.integer n) = some (.finite (Binary64.ofSmallInt n small)) := by
  simpa only [CBody.cast, declared, Option.bind_some] using integer_float64 n small

theorem cast_size (type : String) (x : Binary64.Value)
    (declared : interface.types type = some .size)
    (bounded : 0 ≤ Binary64.truncateInteger x ∧ Binary64.truncateInteger x < 2 ^ 64) :
    CBody.cast type (.finite x) = some (.integer (Binary64.truncateInteger x)) := by
  simpa only [CBody.cast, declared, Option.bind_some] using finite_size x bounded

theorem eval_integer_cast (env : CBody.Locals) (heap : Heap) (type name : String) (n : Int)
    (declared : interface.types type = some .float64) (bound : env name = some (.integer n))
    (small : n.natAbs < 2 ^ 53) :
    CBody.eval env heap (.cast type (.id name)) = some (.finite (Binary64.ofSmallInt n small)) := by
  simpa only [CBody.eval, CBody.evalWith, CBody.resolve, bound, Option.orElse_some, Option.bind_some,
    CBody.expressionCast_ordinary (show CBody.zeroLiteral (.id name) = false by rfl)] using
    cast_integer type n declared small

theorem eval_size_cast (env : CBody.Locals) (heap : Heap) (type name : String) (x : Binary64.Value)
    (declared : interface.types type = some .size) (bound : env name = some (.finite x))
    (bounded : 0 ≤ Binary64.truncateInteger x ∧ Binary64.truncateInteger x < 2 ^ 64) :
    CBody.eval env heap (.cast type (.id name)) = some (.integer (Binary64.truncateInteger x)) := by
  simpa only [CBody.eval, CBody.evalWith, CBody.resolve, bound, Option.orElse_some, Option.bind_some,
    CBody.expressionCast_ordinary (show CBody.zeroLiteral (.id name) = false by rfl)] using
    cast_size type x declared bounded

end Rumoca.CIntegerConversions
