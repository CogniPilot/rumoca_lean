import RumocaCore.Tensor.Operators
import RumocaCore.Real.Classification
import RumocaCore.Real.MultiplicationResult

/-! Rank-preserving numerical results and a total finiteness detector.
The detector describes the complete tensor, not just a successful example or
the returned coordinate of an otherwise unchecked computation. It imposes no
FMI/eFMI status policy. Operations are semantic whole-tensor operations; compiler
lowering does not enumerate elements. -/
namespace Rumoca.Solve.Tensor.Numerical
open Rumoca.Tensor
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096

abbrev Result (shape : Shape) := Value Float64.Number shape
abbrev Bits (shape : Shape) := Value (BitVec 64) shape

def encode (result : Result shape) : Bits shape :=
  result.mapWith Float64.Number.encode

def allFinite (result : Result shape) : Bool :=
  result.data.all Float64.Number.isFinite

def allFiniteBits (bits : Bits shape) : Bool := bits.data.all Float64.finiteBits

theorem allFinite_iff (result : Result shape) :
    allFinite result = true ↔ ∀ i : Fin shape.volume, ∃ value, result[i] = .finite value := by
  simp only [allFinite, Vector.all_eq_true]
  constructor
  · intro h i
    exact (Float64.Number.isFinite_iff _).1 (h i.val i.isLt)
  · intro h i hi
    exact (Float64.Number.isFinite_iff _).2 (h ⟨i, hi⟩)

theorem allFinite_false_iff (result : Result shape) :
    allFinite result = false ↔ ∃ i : Fin shape.volume,
      result[i] = .negativeInfinity ∨ result[i] = .positiveInfinity ∨ result[i] = .nan := by
  simp only [allFinite, Vector.all_eq_false]
  constructor
  · rintro ⟨i, hi, failed⟩
    exact ⟨⟨i, hi⟩, (Float64.Number.not_finite_iff _).1 (Bool.eq_false_iff.2 failed)⟩
  · rintro ⟨i, failed⟩
    exact ⟨i.val, i.isLt, Bool.eq_false_iff.1 ((Float64.Number.not_finite_iff _).2 failed)⟩

theorem allFiniteBits_iff (bits : Bits shape) :
    allFiniteBits bits = true ↔
      ∀ i : Fin shape.volume, ∃ value, bits[i] = (Binary64.toBits value).val := by
  simp only [allFiniteBits, Vector.all_eq_true]
  constructor
  · intro h i
    exact (Float64.finiteBits_iff _).1 (h i.val i.isLt)
  · intro h i hi
    exact (Float64.finiteBits_iff _).2 (h ⟨i, hi⟩)

theorem allFiniteBits_encode (result : Result shape) :
    allFiniteBits (encode result) = allFinite result := by
  apply Bool.eq_iff_iff.mpr
  simp only [allFiniteBits, allFinite, Vector.all_eq_true]
  simp [encode, Value.mapWith, Float64.finiteBits_encode]

noncomputable section

def multiply (a b : Value Binary64.Value shape) : Result shape :=
  a.zipWith Binary64.mulResult b

theorem multiply_spec (a b : Value Binary64.Value shape) (i : Fin shape.volume) :
    Binary64.MultipliesResult a[i] b[i] (multiply a b)[i] := by
  simp only [multiply, Fin.getElem_fin, Value.getElem_zipWith]
  exact Binary64.mulResult_spec _ _

theorem multiply_unique (a b : Value Binary64.Value shape) (result : Result shape)
    (spec : ∀ i : Fin shape.volume, Binary64.MultipliesResult a[i] b[i] result[i]) :
    result = multiply a b := by
  apply Value.ext
  intro i hi
  exact Binary64.multipliesResult_unique (spec ⟨i, hi⟩) (multiply_spec a b ⟨i, hi⟩)

/-- Detection succeeds exactly on the independently specified finite product
domain. Finite operands alone are not enough. -/
theorem multiply_allFinite_iff (a b : Value Binary64.Value shape) :
    allFinite (multiply a b) = true ↔ ∀ i : Fin shape.volume, Binary64.finiteProduct a[i] b[i] := by
  rw [allFinite_iff]
  constructor
  · intro h i
    obtain ⟨value, same⟩ := h i
    have spec := multiply_spec a b i
    rw [same] at spec
    exact spec.1
  · intro h i
    refine ⟨Binary64.roundedMul a[i] b[i], ?_⟩
    simpa only [multiply, Fin.getElem_fin, Value.getElem_zipWith] using
      Binary64.mulResult_finite a[i] b[i] (h i)

theorem multiply_detects_iff (a b : Value Binary64.Value shape) :
    allFiniteBits (encode (multiply a b)) = false ↔
      ∃ i : Fin shape.volume, ¬ Binary64.finiteProduct a[i] b[i] := by
  simp only [allFiniteBits_encode, Bool.eq_false_iff, ne_eq, multiply_allFinite_iff]
  push Not
  rfl

end
end Rumoca.Solve.Tensor.Numerical
