import RumocaC.StringLiteralContents
import RumocaC.LiteralPoolStorage

/-! Immutable literal bytes and C-string contents at installation and a later
read-only-framed heap. Installation freshness and native layout stay separate. -/
namespace Rumoca.CLiteral
open CMemory CStringMemory

/-- Bytes and C-string contents at both installation and an admitted later heap. -/
def StoredContents (signed : Bool) (installed heap : Heap)
    (address : Address) (text : String) : Prop :=
  Stored signed installed address text ∧ Contents installed address (content text) ∧
  Stored signed heap address text ∧ Contents heap address (content text)

theorem stored_contents {reserved : List String} (pool : Pool reserved)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (text : String) (address : Address)
    (bound : pool.addresses firstBlock text = some address) :
    StoredContents signed (pool.install before firstBlock signed) heap address text := by
  have installed := pool.storage_valid before firstBlock signed text address bound
  have kept := installed.preserved frame
  exact ⟨installed, literal_contents installed, kept, literal_contents kept⟩

end Rumoca.CLiteral
