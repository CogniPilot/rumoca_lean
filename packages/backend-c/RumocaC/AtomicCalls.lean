import RumocaC.AtomicStorage

/-! Typed call specifications for the selected non-explicit C11 atomic Boolean
functions. They use sequentially consistent order. The observable labels retain
atomic operation order for later interleaving proofs; host-only observation
will erase them. These definitions do not certify native library bindings. -/
noncomputable section
namespace Rumoca.CAtomicBoolean.Calls
open CTree CMemory

inductive Event where
  | exchange (address : Address) (old next : Bool)
  | write (address : Address) (next : Bool)
  deriving DecidableEq, Repr

def exchangeSignature : Signature :=
  ⟨"_Bool", "atomic_exchange", [⟨"volatile atomic_bool *", "object", false⟩, ⟨"_Bool", "desired", false⟩]⟩

def writeSignature : Signature :=
  ⟨"void", "atomic_store", [⟨"volatile atomic_bool *", "object", false⟩, ⟨"_Bool", "desired", false⟩]⟩

variable [interface : CInterface]

theorem arguments_converted (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer) (p : Address) (next : Bool) :
    CCalls.Events.convertedArguments exchangeSignature.parameters [.pointer (some p), value next] =
      some [.pointer (some p), value next] := by
  cases next <;> simp [CCalls.Events.convertedArguments, exchangeSignature, CCalls.parameters,
    CCalls.parameterType, CBody.cast, CBody.bind, boolean, pointer, value, convert, Value.truth]

def exchangeExternal (tag : Event → E) (boolean : interface.types "_Bool" = some .boolean) :
    CCalls.Events.External E where
  signature := exchangeSignature
  execute args before events result after := ∃ p old next,
    args = [.pointer (some p), value next] ∧
    CAtomicBoolean.exchange before p next = some (old, after) ∧
    events = [tag (.exchange p old next)] ∧ result = value old
  result_typed := by
    rintro args before events result after ⟨p, old, next, rfl, step, rfl, rfl⟩
    cases old <;> simp [exchangeSignature, CCalls.returnCast, CBody.cast, boolean, value, convert, Value.truth]
  readonly := by
    rintro args before events result after ⟨p, old, next, rfl, step, rfl, rfl⟩
    exact exchange_readonly step

def writeExternal (tag : Event → E) : CCalls.Events.External E where
  signature := writeSignature
  execute args before events result after := ∃ p next,
    args = [.pointer (some p), value next] ∧
    CAtomicBoolean.write before p next = some after ∧
    events = [tag (.write p next)] ∧ result = .void
  result_typed := by
    rintro args before events result after ⟨p, next, rfl, step, rfl, rfl⟩
    rfl
  readonly := by
    rintro args before events result after ⟨p, next, rfl, step, rfl, rfl⟩
    exact write_readonly step

theorem exchange_executes (tag : Event → E) (boolean : interface.types "_Bool" = some .boolean)
    (step : CAtomicBoolean.exchange before p next = some (old, after)) :
    (exchangeExternal tag boolean).execute [.pointer (some p), value next] before
      [tag (.exchange p old next)] (value old) after :=
  ⟨p, old, next, rfl, step, rfl, rfl⟩

theorem write_executes (tag : Event → E)
    (step : CAtomicBoolean.write before p next = some after) :
    (writeExternal tag).execute [.pointer (some p), value next] before
      [tag (.write p next)] .void after :=
  ⟨p, next, rfl, step, rfl, rfl⟩

theorem exchange_unique (tag : Event → E) (boolean : interface.types "_Bool" = some .boolean)
    (step : CAtomicBoolean.exchange before p next = some (old, after))
    (executed : (exchangeExternal tag boolean).execute [.pointer (some p), value next]
      before events result heap) :
    events = [tag (.exchange p old next)] ∧ result = value old ∧ heap = after := by
  obtain ⟨q, observed, desired, args, operation, rfl, rfl⟩ := executed
  have addresses : p = q := by simpa using (List.cons.inj args).1
  have values : next = desired := value_injective (List.cons.inj (List.cons.inj args).2).1
  subst q
  subst desired
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (operation.symm.trans step))
  exact ⟨rfl, rfl, rfl⟩

theorem write_unique (tag : Event → E)
    (step : CAtomicBoolean.write before p next = some after)
    (executed : (writeExternal tag).execute [.pointer (some p), value next]
      before events result heap) :
    events = [tag (.write p next)] ∧ result = .void ∧ heap = after := by
  obtain ⟨q, desired, args, operation, rfl, rfl⟩ := executed
  have addresses : p = q := by simpa using (List.cons.inj args).1
  have values : next = desired := value_injective (List.cons.inj (List.cons.inj args).2).1
  subst q
  subst desired
  exact ⟨rfl, rfl, Option.some.inj (operation.symm.trans step)⟩

/-- A valid atomic call terminates with precisely its specified memory effect
and observable operation. This is the selected C11 binding's contract, not a
termination claim for arbitrary host callbacks. -/
theorem exchange_behaviors (program : CCalls.Events.Program E) (tag : Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (bound : program.externals "atomic_exchange" = some (exchangeExternal tag boolean))
    (operation : CAtomicBoolean.exchange before p next = some (old, after)) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "atomic_exchange" [.pointer (some p), value next] before .done) behavior ↔
      behavior = .terminates [tag (.exchange p old next)] ⟨value old, after⟩ :=
  CCalls.Events.external_behaviors program bound (arguments_converted boolean pointer p next)
    (exchange_executes tag boolean operation)
    (fun _ _ _ executed => exchange_unique tag boolean operation executed) behavior

theorem write_behaviors (program : CCalls.Events.Program E) (tag : Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (bound : program.externals "atomic_store" = some (writeExternal tag))
    (operation : CAtomicBoolean.write before p next = some after) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "atomic_store" [.pointer (some p), value next] before .done) behavior ↔
      behavior = .terminates [tag (.write p next)] ⟨.void, after⟩ :=
  CCalls.Events.external_behaviors program bound (arguments_converted boolean pointer p next)
    (write_executes tag operation)
    (fun _ _ _ executed => write_unique tag operation executed) behavior

theorem exchange_step (program : CCalls.Events.Program E) (tag : Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (bound : program.externals "atomic_exchange" = some (exchangeExternal tag boolean))
    (arguments : CCalls.Events.convertedArguments exchangeSignature.parameters args =
      some [.pointer (some p), value next])
    (operation : CAtomicBoolean.exchange before p next = some (old, after)) :
    CCalls.Events.Step program (.calling "atomic_exchange" args before stack)
      [tag (.exchange p old next)] (.returning (value old) after stack) :=
  .external bound arguments (exchange_executes tag boolean operation)

theorem write_step (program : CCalls.Events.Program E) (tag : Event → E)
    (bound : program.externals "atomic_store" = some (writeExternal tag))
    (arguments : CCalls.Events.convertedArguments writeSignature.parameters args =
      some [.pointer (some p), value next])
    (operation : CAtomicBoolean.write before p next = some after) :
    CCalls.Events.Step program (.calling "atomic_store" args before stack)
      [tag (.write p next)] (.returning .void after stack) :=
  .external bound arguments (write_executes tag operation)

end Rumoca.CAtomicBoolean.Calls
