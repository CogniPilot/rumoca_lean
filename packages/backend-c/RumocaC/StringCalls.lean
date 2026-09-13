import RumocaC.StringOperations
import RumocaC.CallEventChoices
import RumocaC.CallCasts

/-! Selected C11 string-library bindings in the shared typed call machine.
Each result is derived from null-terminated character memory. The routines do
not change that memory; strcmp admits every representable result of the correct
sign. Native library correspondence, headers and absence of hidden allocation
remain explicit obligations; this module does not prove a libc implementation. -/
noncomputable section
namespace Rumoca.CStringCalls
open CMemory CTree CStringMemory CStringOperations

def lengthSignature : Signature := ⟨"size_t", "strlen", [⟨"const char *", "s", false⟩]⟩
def spanSignature : Signature :=
  ⟨"size_t", "strspn", [⟨"const char *", "s1", false⟩, ⟨"const char *", "s2", false⟩]⟩
def compareSignature : Signature :=
  ⟨"int", "strcmp", [⟨"const char *", "s1", false⟩, ⟨"const char *", "s2", false⟩]⟩

variable [interface : CInterface]

def lengthExternal (size : interface.types "size_t" = some .size) : CCalls.Events.External E where
  signature := lengthSignature
  execute args before events result after := ∃ p bytes,
    args = [.pointer (some p)] ∧ Contents before p bytes ∧ bytes.length < 2^64 ∧
      events = [] ∧ result = .integer bytes.length ∧ after = before
  result_typed := by
    rintro args before events result after ⟨p, bytes, rfl, stored, bound, rfl, rfl, rfl⟩
    exact CCalls.Casts.sizeReturn size bytes.length bound
  readonly := by
    rintro args before events result after ⟨p, bytes, rfl, stored, bound, rfl, rfl, rfl⟩
    exact .refl _

def spanExternal (size : interface.types "size_t" = some .size) : CCalls.Events.External E where
  signature := spanSignature
  execute args before events result after := ∃ p q bytes accepted,
    args = [.pointer (some p), .pointer (some q)] ∧
    Contents before p bytes ∧ Contents before q accepted ∧ bytes.length < 2^64 ∧
    events = [] ∧ result = .integer (span bytes accepted) ∧ after = before
  result_typed := by
    rintro args before events result after ⟨p, q, bytes, accepted, rfl, stored, allowed, bound, rfl, rfl, rfl⟩
    exact CCalls.Casts.sizeReturn size _ (lt_of_le_of_lt (span_le_length bytes accepted) bound)
  readonly := by
    rintro args before events result after ⟨p, q, bytes, accepted, rfl, stored, allowed, bound, rfl, rfl, rfl⟩
    exact .refl _

def compareExternal (integer : interface.types "int" = some .int32) : CCalls.Events.External E where
  signature := compareSignature
  execute args before events result after := ∃ p q left right n,
    args = [.pointer (some p), .pointer (some q)] ∧ Contents before p left ∧ Contents before q right ∧
    (-(2^31) ≤ n ∧ n < 2^31) ∧ Comparison left right n ∧
    events = [] ∧ result = .integer n ∧ after = before
  result_typed := by
    rintro args before events result after ⟨p, q, left, right, n, rfl, leftStored, rightStored, bound,
      compared, rfl, rfl, rfl⟩
    exact CCalls.Casts.intReturn integer n bound
  readonly := by
    rintro args before events result after ⟨p, q, left, right, n, rfl, leftStored, rightStored, bound,
      compared, rfl, rfl, rfl⟩
    exact .refl _

theorem single_arguments (pointer : interface.types "const char *" = some .pointer) (p : Address) :
    CCalls.Events.convertedArguments lengthSignature.parameters [.pointer (some p)] = some [.pointer (some p)] := by
  simp [CCalls.Events.convertedArguments, lengthSignature, CCalls.parameters, CCalls.parameterType,
    CBody.cast, CBody.bind, pointer, convert]

theorem pair_arguments (pointer : interface.types "const char *" = some .pointer) (p q : Address) :
    CCalls.Events.convertedArguments spanSignature.parameters [.pointer (some p), .pointer (some q)] =
      some [.pointer (some p), .pointer (some q)] := by
  simp [CCalls.Events.convertedArguments, spanSignature, CCalls.parameters, CCalls.parameterType,
    CBody.cast, CBody.bind, pointer, convert]

theorem length_effect (size : interface.types "size_t" = some .size)
    (stored : Contents before p bytes) :
    (lengthExternal (E := E) size).execute [.pointer (some p)] before events result after ↔
      bytes.length < 2^64 ∧ events = [] ∧ result = .integer bytes.length ∧ after = before := by
  constructor
  · rintro ⟨q, content, args, other, bound, rfl, rfl, rfl⟩
    have same : p = q := by simpa using (List.cons.inj args).1
    subst q
    have sameBytes := stored.unique other
    subst content
    exact ⟨bound, rfl, rfl, rfl⟩
  · rintro ⟨bound, rfl, rfl, rfl⟩
    exact ⟨p, bytes, rfl, stored, bound, rfl, rfl, rfl⟩

theorem span_effect (size : interface.types "size_t" = some .size)
    (stored : Contents before p bytes) (allowed : Contents before q accepted) :
    (spanExternal (E := E) size).execute [.pointer (some p), .pointer (some q)] before events result after ↔
      bytes.length < 2^64 ∧ events = [] ∧ result = .integer (span bytes accepted) ∧ after = before := by
  constructor
  · rintro ⟨p', q', content, set, args, other, otherSet, bound, rfl, rfl, rfl⟩
    have first : p = p' := by simpa using (List.cons.inj args).1
    have second : q = q' := by simpa using (List.cons.inj (List.cons.inj args).2).1
    subst p'
    subst q'
    have sameBytes := stored.unique other
    have sameSet := allowed.unique otherSet
    subst content
    subst set
    exact ⟨bound, rfl, rfl, rfl⟩
  · rintro ⟨bound, rfl, rfl, rfl⟩
    exact ⟨p, q, bytes, accepted, rfl, stored, allowed, bound, rfl, rfl, rfl⟩

theorem compare_effect (integer : interface.types "int" = some .int32)
    (leftStored : Contents before p left) (rightStored : Contents before q right) :
    (compareExternal (E := E) integer).execute [.pointer (some p), .pointer (some q)] before events result after ↔
      ∃ n : Int, (-(2^31) ≤ n ∧ n < 2^31) ∧ Comparison left right n ∧
        events = [] ∧ result = .integer n ∧ after = before := by
  constructor
  · rintro ⟨p', q', a, b, n, args, otherLeft, otherRight, bound, compared, rfl, rfl, rfl⟩
    have first : p = p' := by simpa using (List.cons.inj args).1
    have second : q = q' := by simpa using (List.cons.inj (List.cons.inj args).2).1
    subst p'
    subst q'
    have sameLeft := leftStored.unique otherLeft
    have sameRight := rightStored.unique otherRight
    subst a
    subst b
    exact ⟨n, bound, compared, rfl, rfl, rfl⟩
  · rintro ⟨n, bound, compared, rfl, rfl, rfl⟩
    exact ⟨p, q, left, right, n, rfl, leftStored, rightStored, bound, compared, rfl, rfl, rfl⟩

end Rumoca.CStringCalls
