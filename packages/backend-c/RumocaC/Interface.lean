import RumocaC.Memory

/-! Header bindings supplied by a target adapter. The C machine implements
operations over these named constants and declared types. There is no global
default instance: every adapter proof selects its own concrete dictionary. -/
namespace Rumoca

class CInterface where
  constants : String → Option CMemory.Value
  types : String → Option CMemory.CType

end Rumoca
