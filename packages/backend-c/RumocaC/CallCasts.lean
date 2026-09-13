import RumocaC.TypedCalls
import RumocaC.LoopProofs

/-! Named and return casts through explicit target type bindings. Keeping the
conversion proof abstract avoids unfolding integer-width arithmetic while
composing call contracts. -/
namespace Rumoca.CCalls.Casts
open CMemory
variable [interface : CInterface]

theorem named (spelling : String) (type : CType) (value result : Value)
    (typed : interface.types spelling = some type) (converted : convert type value = some result) :
    CBody.cast spelling value = some result := by
  simp only [CBody.cast, typed, bind, Option.bind_some, converted]

theorem valueReturn (spelling : String) (value result : Value)
    (nonvoid : spelling ≠ "void") (converted : CBody.cast spelling value = some result) :
    returnCast spelling value = some result := by
  simp only [returnCast, if_neg nonvoid, converted]

theorem sizeReturn (size : interface.types "size_t" = some .size) (n : Nat) (bound : n < 2^64) :
    returnCast "size_t" (.integer n) = some (.integer n) :=
  valueReturn "size_t" (.integer n) (.integer n) (by decide)
    (named "size_t" .size (.integer n) (.integer n) size (CLoops.convert_size_nat n bound))

theorem intReturn (integer : interface.types "int" = some .int32) (n : Int)
    (bound : -(2^31) ≤ n ∧ n < 2^31) :
    returnCast "int" (.integer n) = some (.integer n) :=
  valueReturn "int" (.integer n) (.integer n) (by decide)
    (named "int" .int32 (.integer n) (.integer n) integer (by simp only [convert, if_pos bound]))

end Rumoca.CCalls.Casts
