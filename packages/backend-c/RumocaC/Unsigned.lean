import Std

/-! Integer conversion to an unsigned destination with an explicit value width.
The result is the unique in-range integer differing by a multiple of one more
than the maximum value (N1570 §6.3.1.3). The standard-library BitVec bridge
supplies the bit representation. Platform type selection remains explicit. -/
namespace Rumoca.CUnsigned

def modulus (width : Nat) : Int := 2 ^ width

theorem modulus_pos (width : Nat) : 0 < modulus width := by
  change 0 < (2 : Int) ^ width
  exact Int.pow_pos (by decide)

def value (width : Nat) (input : Int) : Int := input % modulus width

def Converts (width : Nat) (input output : Int) : Prop :=
  0 ≤ output ∧ output < modulus width ∧ ∃ steps : Int, input = output + steps * modulus width

theorem value_correct (width : Nat) (input : Int) : Converts width input (value width input) := by
  refine ⟨Int.emod_nonneg _ (Int.ne_of_gt (modulus_pos width)),
    Int.emod_lt_of_pos _ (modulus_pos width), input / modulus width, ?_⟩
  exact (Int.emod_add_ediv_mul input (modulus width)).symm

theorem value_unique (h : Converts width input output) : output = value width input := by
  obtain ⟨nonnegative, bound, steps, same⟩ := h
  simp [value, same, Int.add_emod, Int.emod_eq_of_lt nonnegative bound]

theorem value_in_range (nonnegative : 0 ≤ input) (bound : input < modulus width) :
    value width input = input := Int.emod_eq_of_lt nonnegative bound

theorem value_idempotent (width : Nat) (input : Int) :
    value width (value width input) = value width input := Int.emod_emod _ _

theorem value_bits (width : Nat) (input : Int) :
    value width input = ((BitVec.ofInt width input).toNat : Int) := by
  have nonnegative : 0 ≤ input % (2 : Int) ^ width := (value_correct width input).1
  simp [BitVec.toNat_ofInt, value, modulus]
  omega

end Rumoca.CUnsigned
