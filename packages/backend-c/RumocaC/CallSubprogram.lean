import RumocaC.CallSites

/-! A proof-only restriction of a function table. Actual execution is unchanged
whenever its current call belongs to the selected domain. This allows a closed
call-domain invariant to reuse the ordinary operand-policy preservation proof
without assuming that unrelated functions obey that domain's policy. -/
noncomputable section
namespace Rumoca.CCallSites.Subprogram
open CTree CMemory CCalls
variable [CInterface] {E : Type} {program : Events.Program E}

def restrict (program : Events.Program E) (allowed : String → Bool) : Events.Program E where
  internal := ⟨fun name => if allowed name then program.internal.definitions name else none, program.internal.kernel⟩
  addresses := program.addresses
  externals := program.externals
  disjoint := by
    intro name fn found
    simp [program.disjoint name fn found]
  names := program.names

def AtAllowed (allowed : String → Bool) : Typed.State → Prop
  | .calling name _ _ _ => allowed name = true
  | _ => True

theorem internal_same (current : AtAllowed allowed state) :
    Events.internalNext (restrict program allowed) state = Events.internalNext program state := by
  cases state with
  | calling name args heap stack =>
    simp only [AtAllowed] at current
    simp only [Events.internalNext, Typed.nextWith, restrict, current, ↓reduceIte]
  | body state => cases state <;> rfl
  | kernel state => cases state <;> rfl
  | _ => rfl

theorem event_same (current : AtAllowed allowed state) :
    Events.Step (restrict program allowed) state events after ↔ Events.Step program state events after := by
  constructor
  · intro step
    cases step with
    | internal next => exact .internal ((internal_same current).symm.trans next)
    | external found converted executed => exact .external found converted executed
  · intro step
    cases step with
    | internal next => exact .internal ((internal_same current).trans next)
    | external found converted executed => exact .external found converted executed

theorem functions_admit
    (functions : ∀ name, allowed name = true → ∀ fn, program.internal.definitions name = some (.tree fn) →
      ∀ stmt ∈ fn.body, Admits permitted stmt) :
    ProgramAdmits permitted (restrict program allowed).internal := by
  intro name fn found
  change (if allowed name then program.internal.definitions name else none) = some (.tree fn) at found
  split at found
  · exact functions name ‹allowed name = true› fn found
  · contradiction

/-- Preserve the original, unrestricted program's actual transition. Only
reachable definitions need the operand policy; the proof table restriction is
erased by event equivalence at the current admitted call. -/
theorem event_ready (program : Events.Program E) (allowed : String → Bool)
    (functions : ∀ name, allowed name = true → ∀ fn, program.internal.definitions name = some (.tree fn) →
      ∀ stmt ∈ fn.body, Admits permitted stmt)
    (sound : OperandSound program permitted (fun name _ => allowed name = true))
    (ready : Ready permitted (fun name _ => allowed name = true) before)
    (step : Events.Step program before events after) :
    Ready permitted (fun name _ => allowed name = true) after := by
  have current : AtAllowed allowed before := by
    cases before with
    | calling => exact ready.1
    | _ => trivial
  exact CCallSites.event_ready (restrict program allowed) (functions_admit functions) sound ready
    ((event_same current).mpr step)

end Rumoca.CCallSites.Subprogram
