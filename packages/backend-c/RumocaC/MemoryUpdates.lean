import RumocaC.Memory

namespace Rumoca.CMemory

/-- Repeated writes to one cell retain its last value and the original frame. -/
theorem replace_overwrite (heap : Heap) (address : Address) (first last : Cell) :
    replace (replace heap address first) address last = replace heap address last := by
  funext q
  by_cases same : q = address <;> simp [replace, same]


end Rumoca.CMemory
