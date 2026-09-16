import RumocaC.WriteRegions
import RumocaC.InitializationCompletion

namespace Rumoca.CCalls.InitializationRegion
open CTree CMemory
variable [CInterface]

theorem Ready.destination
    (ready : Ready region env types resultExpr resultType expected returned .done state)
    (selected : CWriteFootprint.current state = some address) : address ∈ region := by
  cases ready with
  | running pending reference heap writes finishes agreement =>
    cases pending with
    | nil => simp [CWriteFootprint.current, CWriteFootprint.loop] at selected
    | cons stmt rest =>
      have head := writes stmt (by simp)
      cases stmt <;> simp only [CLoops.Footprint.AssignsWithin] at head
      case assign target value =>
        obtain ⟨_, _, inside⟩ := head
        have chosen : CBody.lvalue env heap target = some address := by
          change CWriteFootprint.target env heap target = some address at selected
          cases target <;> exact selected
        exact inside heap address chosen
  | finishing => simp [CWriteFootprint.current, CWriteFootprint.loop] at selected
  | returning => simp [CWriteFootprint.current, CWriteFootprint.saved] at selected

theorem Ready.foreign_frame
    (ready : Ready region env types resultExpr resultType expected returned .done state) :
    CWriteFootprint.ForeignFrame protectedRegion program state := by
  cases ready <;> trivial

theorem CompleteReady.destination
    (ready : CompleteReady region env types resultExpr resultType expected returned state)
    (selected : CWriteFootprint.current state = some address) : address ∈ region := by
  rcases ready with ready | ⟨heap, rfl, agreement⟩
  · exact ready.destination selected
  · simp [CWriteFootprint.current] at selected

theorem CompleteReady.foreign_frame
    (ready : CompleteReady region env types resultExpr resultType expected returned state) :
    CWriteFootprint.ForeignFrame protectedRegion program state := by
  rcases ready with ready | ⟨heap, rfl, agreement⟩
  · exact ready.foreign_frame
  · trivial

end Rumoca.CCalls.InitializationRegion
