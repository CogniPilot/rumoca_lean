import RumocaC.LiteralStorage

/-! The selected literal-address environment connects C array decay and
ordinary pointer arguments to immutable character objects. Storage validity
is explicit; no allocator, native linker, or foreign callback is modeled. -/
namespace Rumoca.CLiteral
open CMemory

def Valid (locations : CLiteralAddresses) (signed : Bool) (heap : Heap) : Prop :=
  ∀ source base, locations source = some base → Stored signed heap base source

theorem Valid.preserved (valid : Valid locations signed before)
    (preserved : CReadOnly.Preserves before after) : Valid locations signed after :=
  fun source base bound => (valid source base bound).preserved preserved

variable [interface : CInterface]

/-- In the expression contexts supported by this machine, a literal array
decays to its supplied first-element address. Missing storage bindings reject
evaluation; they do not silently become null pointers or abstract strings. -/
theorem eval_string (bound : interface.literals source = some base) :
    CBody.eval env heap (.str source) = some (.pointer (some base)) := by
  simp [CBody.eval, bound]

theorem eval_string_missing (missing : interface.literals source = none) :
    CBody.eval env heap (.str source) = none := by
  simp [CBody.eval, missing]

theorem pointer_argument (bound : interface.literals source = some base)
    (type : interface.types spelling = some .pointer) :
    CBody.eval env heap (.cast spelling (.str source)) = some (.pointer (some base)) := by
  simp [CBody.eval, bound, CBody.cast, type, convert]

/-- Indexing the actual string expression reads the represented character,
including its zero terminator and the chosen signed-char interpretation. -/
theorem eval_index (valid : Valid interface.literals signed heap)
    (bound : interface.literals source = some base)
    (atByte : (bytes source)[index]? = some byte) :
    CBody.eval env heap (.index (.str source) (.nat index)) =
      some (.integer (CCharacter.value signed byte)) := by
  have loaded := (valid source base bound).load atByte
  simp [CBody.eval, bound, Value.address, loaded]

/-- Actual rendered bytes and expression execution share the same object
address and byte storage after every modeled preprocessing sequence. -/
theorem rendered_pointer (valid : Valid interface.literals signed heap)
    (bound : interface.literals source = some base)
    (steps : Relation.ReflTransGen CString.Rewrite
      (CTree.Expr.render (.str source)).toList processed)
    (decoded : CString.Denotes processed actualBytes) :
    CBody.eval env heap (.str source) = some (.pointer (some base)) ∧
      ∀ index byte, actualBytes[index]? = some byte →
        readByte heap (base.index index) = some byte :=
  ⟨eval_string bound, rendered_memory source (valid source base bound) _ steps _ decoded⟩

noncomputable section
theorem Valid.after_steps (valid : Valid interface.literals signed (CReadOnly.typedHeap s))
    (steps : Transition.Reaches (CCalls.Typed.machine program).step s t) :
    Valid interface.literals signed (CReadOnly.typedHeap t) :=
  valid.preserved (CReadOnly.typed_reaches steps)
end
end Rumoca.CLiteral
