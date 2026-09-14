import RumocaC.StoreInvariant
import RumocaC.ArrayStore

noncomputable section
namespace Rumoca.CStoreInvariant
open CMemory
variable {R : Heap → Heap → Prop} (stable : Stable R)
  (trans : ∀ {a b c}, R a b → R b c → R a c)
include stable trans

section
variable [CInterface]

theorem body_reaches (path : Transition.Reaches CBody.machine.step before after) :
    R (CReadOnly.bodyHeap before) (CReadOnly.bodyHeap after) := by
  induction path with
  | refl => exact stable.refl _
  | next step _ ih => exact trans (body_next stable step) ih

theorem body_run (executed : CBody.run count before = some after) :
    R (CReadOnly.bodyHeap before) (CReadOnly.bodyHeap after) :=
  body_reaches stable trans (CBody.run_reaches executed)

end

/-- Host-buffer transfers use the same checked store invariant as internal
execution. Conversion and rejection remain those of the original store. -/
theorem array_run (executed : ArrayStore.run heap base values count = some after) : R heap after := by
  induction count generalizing after with
  | zero => cases Option.some.inj executed; exact stable.refl _
  | succ count ih =>
    simp only [ArrayStore.run, Option.bind_eq_bind, Option.bind_eq_some_iff] at executed
    obtain ⟨prior, priorRun, final⟩ := executed
    split at final
    · exact trans (ih priorRun) (stable.store _ _ _ _ final)
    · contradiction

end Rumoca.CStoreInvariant
end
