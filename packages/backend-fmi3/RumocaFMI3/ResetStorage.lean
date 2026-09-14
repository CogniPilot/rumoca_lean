import RumocaFMI3.Reset
import RumocaC.StorageTransfer

namespace Rumoca.FMI3
open CMemory

theorem Reset.Storage.preserved (stored : Reset.Storage heap p) (preserved : CStorage.Preserves heap after) :
    Reset.Storage after p := by
  have keep {address type} (cell : Reset.Writable heap address type) : Reset.Writable after address type := by
    obtain ⟨old, found⟩ := cell
    exact preserved.cell found
  exact ⟨keep stored.state, keep stored.time, keep stored.minimum, keep stored.event,
    keep stored.completed, keep stored.stop, keep stored.stopDefined, keep stored.mode⟩

end Rumoca.FMI3
