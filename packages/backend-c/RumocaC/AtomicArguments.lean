import RumocaC.AtomicCalls

/-! Actual atomic parameter conversion and operation effects. -/
namespace Rumoca.CAtomicBoolean.Calls
open CTree CMemory CCalls CCalls.Events
variable [interface : CInterface]

/-- Actual parameter conversion preserves the Boolean argument and requires
an ordinary pointer value. Validity of the selected atomic cell is separate. -/
theorem converted_shape (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (converted : convertedArguments exchangeSignature.parameters [object, value busy] = some values) :
    ∃ address, object = .pointer address ∧ values = [.pointer address, value busy] := by
  cases object <;> cases busy <;>
    simp [convertedArguments, exchangeSignature, parameters, parameterType, CBody.cast,
      CBody.bind, boolean, pointer, value, convert, Value.truth] at converted ⊢
  all_goals exact converted.symm

/-- A completed exchange uses the Boolean supplied by the generated operand;
parameter casting cannot turn reservation into release. -/
theorem exchange_from_arguments (tag : Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (converted : convertedArguments exchangeSignature.parameters [object, value desired] = some values)
    (executed : (exchangeExternal tag boolean).execute values before events result after) :
    ∃ address observed,
      object = .pointer (some address) ∧
      exchange before address desired = some (observed, after) ∧
      events = [tag (.exchange address observed desired)] ∧ result = value observed := by
  obtain ⟨address, rfl, rfl⟩ := converted_shape boolean pointer converted
  obtain ⟨target, observed, nextValue, arguments, operation, trace, result⟩ := executed
  have same : address = some target := by simpa using (List.cons.inj arguments).1
  have desiredSame : desired = nextValue := value_injective (List.cons.inj (List.cons.inj arguments).2).1
  subst address
  subst nextValue
  exact ⟨target, observed, rfl, operation, trace, result⟩

theorem write_from_arguments (tag : Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (converted : convertedArguments writeSignature.parameters [object, value desired] = some values)
    (executed : (writeExternal tag).execute values before events result after) :
    ∃ address,
      object = .pointer (some address) ∧ write before address desired = some after ∧
      events = [tag (.write address desired)] ∧ result = .void := by
  obtain ⟨address, rfl, rfl⟩ := converted_shape boolean pointer converted
  obtain ⟨target, nextValue, arguments, operation, trace, result⟩ := executed
  have same : address = some target := by simpa using (List.cons.inj arguments).1
  have desiredSame : desired = nextValue := value_injective (List.cons.inj (List.cons.inj arguments).2).1
  subst address
  subst nextValue
  exact ⟨target, rfl, operation, trace, result⟩

end Rumoca.CAtomicBoolean.Calls
