import RumocaC.Character
import RumocaC.ReadOnly
import RumocaC.StringLiteral

/-! Symbolic character objects for the selected eight-bit C profile. Literal
bytes come from the independent printer contract; signed character values use
the explicit two's-complement interpretation in `CCharacter`.

`install` constructs initial symbolic storage, not a native allocator. It
establishes non-vacuity and preserves any previously present read-only cells
when its block is fresh. Literal address selection, array-to-pointer decay,
function binding and external callbacks require separate contracts. -/
namespace Rumoca.CLiteral
open CMemory

def bytes (source : String) : List UInt8 := source.toUTF8.data.toList ++ [0]

def cell (signed : Bool) (byte : UInt8) : Cell :=
  ⟨.character signed, false, some (.integer (CCharacter.value signed byte))⟩

def Stored (signed : Bool) (heap : Heap) (base : Address) (source : String) : Prop :=
  ∀ index byte, (bytes source)[index]? = some byte → heap (base.index index) = some (cell signed byte)

def readByte (heap : Heap) (address : Address) : Option UInt8 := do
  let object ← heap address
  let signed ← match object.type with
    | .character signed => some signed
    | _ => none
  let .integer n ← load heap address | none
  return CCharacter.byteOf signed n

theorem Stored.load (stored : Stored signed heap base source)
    (atByte : (bytes source)[index]? = some byte) :
    CMemory.load heap (base.index index) = some (.integer (CCharacter.value signed byte)) := by
  have found := stored index byte atByte
  simp [CMemory.load, found, cell, convert, CCharacter.value_range]

theorem Stored.read_byte (stored : Stored signed heap base source)
    (atByte : (bytes source)[index]? = some byte) :
    readByte heap (base.index index) = some byte := by
  have found := stored index byte atByte
  have loaded := stored.load atByte
  simp [readByte, found, cell, loaded, CCharacter.byteOf_value]

theorem Stored.preserved (stored : Stored signed before base source)
    (preserved : CReadOnly.Preserves before after) : Stored signed after base source := by
  intro index byte atByte
  exact preserved (base.index index) (cell signed byte) (stored index byte atByte) rfl

def install (heap : Heap) (block : Nat) (signed : Bool) (source : String) : Heap := fun address =>
  if address.block = block then
    if address.members = [] then ((bytes source)[address.offset]?).map (cell signed) else none
  else heap address

theorem installed (heap : Heap) (block : Nat) (signed : Bool) (source : String) :
    Stored signed (install heap block signed source) ⟨block, [], 0⟩ source := by
  intro index byte atByte
  simp [install, Address.index, atByte]

theorem install_frame (different : address.block ≠ block) :
    install heap block signed source address = heap address := by
  simp [install, different]

theorem install_preserves (fresh : ∀ address, address.block = block → heap address = none) :
    CReadOnly.Preserves heap (install heap block signed source) := by
  intro address old found readonly
  have different : address.block ≠ block := by
    intro same
    rw [fresh address same] at found
    contradiction
  rw [install_frame different, found]

/-- Every byte denoted by the actual rendered literal is read back from its
character objects, after any modeled preprocessing sequence. -/
theorem rendered_memory (source : String) (stored : Stored signed heap base source)
    (processed : List Char)
    (steps : Relation.ReflTransGen CString.Rewrite (CTree.Expr.render (.str source)).toList processed)
    (actualBytes : List UInt8) (decoded : CString.Denotes processed actualBytes) :
    ∀ index byte, actualBytes[index]? = some byte → readByte heap (base.index index) = some byte := by
  have same := ((CString.render_correct source).2 processed steps actualBytes).mp decoded
  subst actualBytes
  exact fun _ _ atByte => stored.read_byte atByte

noncomputable section
variable [interface : CInterface]

theorem Stored.after_steps (stored : Stored signed (CReadOnly.typedHeap s) base source)
    (steps : Transition.Reaches (CCalls.Typed.machine program).step s t) :
    Stored signed (CReadOnly.typedHeap t) base source :=
  stored.preserved (CReadOnly.typed_reaches steps)

end
end Rumoca.CLiteral
