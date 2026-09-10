import RumocaC.Memory

/-! Header bindings supplied by a target adapter. The C machine implements
operations over these named constants and declared types. There is no global
default instance: every adapter proof selects its own dictionary and supplied
literal addresses. Literal storage validity is a separate heap contract. -/
namespace Rumoca

/-- A selected static literal pool, with one address per literal text. Missing
entries are unsupported, never null pointers. No injectivity is required:
compatible arrays may share storage. This selection does not model every
possible per-occurrence allocation made by a native C compiler. -/
abbrev CLiteralAddresses := String → Option CMemory.Address

class CInterface where
  constants : String → Option CMemory.Value
  types : String → Option CMemory.CType
  literals : CLiteralAddresses := fun _ => none

end Rumoca
