import RumocaC.StringMemory
import Mathlib.Data.List.TakeWhile

/-! C string contents of any emitted literal. Embedded zeros end the C string
even though the remaining literal bytes still exist in the object. This
constructs the string-read premise from the installed literal storage. -/
namespace Rumoca.CStringMemory
open CMemory

def content (source : String) : List UInt8 :=
  source.toUTF8.data.toList.takeWhile (fun byte => byte != 0)

private theorem index_successor (base : Address) (index : Nat) :
    (base.index 1).index index = base.index (index + 1) := by
  cases base
  simp [Address.index, Nat.add_comm, Nat.add_left_comm]

theorem of_terminated (bytes : List UInt8)
    (read : ∀ index byte, (bytes ++ [0])[index]? = some byte →
      CLiteral.readByte heap (base.index index) = some byte) :
    Contents heap base (bytes.takeWhile (fun byte => byte != 0)) := by
  induction bytes generalizing base with
  | nil => exact .nil (by simpa using read 0 0 (by simp))
  | cons byte bytes ih =>
    by_cases zero : byte = 0
    · subst byte
      exact .nil (by simpa using read 0 0 (by simp))
    · have nonzero : (byte != 0) = true := by simpa only [bne_iff_ne] using zero
      rw [List.takeWhile_cons, if_pos nonzero]
      refine .cons zero (by simpa using read 0 byte (by simp)) ?_
      apply ih
      intro index b found
      rw [index_successor]
      exact read (index + 1) b (by simpa using found)

theorem literal_contents (stored : CLiteral.Stored signed heap base source) :
    Contents heap base (content source) :=
  of_terminated source.toUTF8.data.toList (fun _ _ found => stored.read_byte found)

theorem content_eq (nonzero : ∀ byte ∈ source.toUTF8.data.toList, byte ≠ 0) :
    content source = source.toUTF8.data.toList := by
  apply List.takeWhile_eq_self_iff.mpr
  simpa only [bne_iff_ne] using nonzero

end Rumoca.CStringMemory
