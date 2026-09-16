import RumocaFMI3.PrivateReservations
import RumocaC.InvocationRegion

namespace Rumoca.FMI3.InstanceAuthority.Resources
open CTree CMemory CCalls
variable {capacity : Nat}

/-- Once the actual initializer's exact return and retained reservation have
been derived, they discharge the factory boundary for every candidate slot.
Pointer equality identifies the slot only; the ledger supplies its generation. -/
theorem FactoryResult.returned {before : Host.Recording.State}
    {publications : PublicationRegistry.State capacity} {slot : Fin capacity}
    (active : before.ledger.active thread = some call)
    (privateEntry : publications slot = some ⟨call.serial, false⟩)
    (returned : value = Handle.value instances ⟨slot, call.serial⟩) :
    FactoryResult publications before thread instances (Host.Action.complete (E := E) value) := by
  intro candidate chosen found _ action
  have identity := Option.some.inj (found.symm.trans active)
  subst candidate
  have sameValue := Host.Action.complete.inj action
  rw [returned] at sameValue
  have sameAddress := Option.some.inj (Value.pointer.inj sameValue)
  have same : slot = chosen := (AtomicSlots.address_injective instances) sameAddress
  subst chosen
  exact privateEntry

namespace Publication
variable [CInterface] {E : Type} {program : Events.Program E} {policy : Host.Policy}
  {before after : Configuration capacity}

/-- A framed coupled history projects to its resource/publication history and
the same recorded C history with the identical private-value interference frame. -/
theorem framed_history
    (path : Transition.Events.Reaches
      (fun a ticks b => Step program policy instances flags a ticks b ∧
        Host.Recording.InterferenceFrame region tracked serial a.resources.recorded ticks b.resources.recorded)
      before ticks after) :
    Transition.Events.Reaches (Step program policy instances flags) before ticks after ∧
    Transition.Events.Reaches
      (fun a ticks b => Host.Recording.Step program policy a ticks b ∧
        Host.Recording.InterferenceFrame region tracked serial a ticks b)
      before.resources.recorded ticks after.resources.recorded := by
  induction path with
  | refl => exact ⟨.refl _, .refl _⟩
  | next first rest ih => exact ⟨.next first.1 ih.1, .next ⟨first.1.resources.erases, first.2⟩ ih.2⟩

end Publication
end Rumoca.FMI3.InstanceAuthority.Resources
