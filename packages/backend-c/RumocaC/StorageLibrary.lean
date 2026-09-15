import RumocaC.CallStoreInvariant
import RumocaC.Storage
import RumocaC.StringBindings
import RumocaC.AtomicCalls
import RumocaC.MathCalls

/-! Selected string, atomic and math call relations preserve modeled object storage. This does not prove absence of hidden native allocation. -/
noncomputable section
namespace Rumoca.CStorage
open CTree CMemory CCalls CCalls.Events CStoreInvariant

def stable : Stable Preserves :=
  ⟨Preserves.refl, fun _ _ _ _ step => store_preserves step⟩

variable [interface : CInterface] {E : Type}

theorem length_external (size : interface.types "size_t" = some .size) :
    ExternalPreserves Preserves (CStringCalls.lengthExternal (E := E) size) := by
  rintro args before events result after ⟨p, bytes, args, stored, bound, trace, value, rfl⟩
  exact .refl _

theorem span_external (size : interface.types "size_t" = some .size) :
    ExternalPreserves Preserves (CStringCalls.spanExternal (E := E) size) := by
  rintro args before events result after ⟨p, q, bytes, accepted, args, stored, allowed, bound, trace, value, rfl⟩
  exact .refl _

theorem compare_external (integer : interface.types "int" = some .int32) :
    ExternalPreserves Preserves (CStringCalls.compareExternal (E := E) integer) := by
  rintro args before events result after ⟨p, q, left, right, n, args, ls, rs, bound, compared, trace, value, rfl⟩
  exact .refl _

theorem exchange_external (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean) :
    ExternalPreserves Preserves (CAtomicBoolean.Calls.exchangeExternal tag boolean) := by
  rintro args before events result after ⟨p, old, next, args, step, trace, value⟩
  exact CAtomicBoolean.exchange_storage step

theorem write_external (tag : CAtomicBoolean.Calls.Event → E) :
    ExternalPreserves Preserves (CAtomicBoolean.Calls.writeExternal tag) := by
  rintro args before events result after ⟨p, next, args, step, trace, value⟩
  exact CAtomicBoolean.write_storage step

theorem floor_external (double : interface.types "double" = some .float64) :
    ExternalPreserves Preserves (CMathCalls.floorExternal (E := E) double) := by
  rintro args before events result after ⟨x, args, trace, value, rfl⟩
  exact .refl _

theorem rounding_external (integer : interface.types "int" = some .int32)
    (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31) :
    ExternalPreserves Preserves (CMathCalls.roundingExternal (E := E) integer observed range) := by
  rintro args before events result after ⟨args, trace, value, rfl⟩
  exact .refl _

theorem string_library (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32)
    (found : CStringCalls.library (E := E) size integer name = some fn) :
    ExternalPreserves Preserves fn := by
  unfold CStringCalls.library at found
  split at found
  · cases Option.some.inj found; exact length_external size
  · cases Option.some.inj found; exact span_external size
  · cases Option.some.inj found; exact compare_external integer
  · contradiction
end Rumoca.CStorage
