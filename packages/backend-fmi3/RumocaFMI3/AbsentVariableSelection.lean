import RumocaFMI3.AbsentVariableRuntime
import RumocaFMI3.AbsentVariableMetadata

namespace Rumoca.FMI3.AbsentVariables
open CMemory CCalls.Events

/-- A correctly typed selection from absent XML declarations has zero
references and zero serialized elements, for every per-variable extent.
Counts are compared as naturals, without truncating them to machine words. -/
theorem selected_cardinalities_zero (absent : Absent root ty)
    (selected : List XML.Element) (extent : XML.Element → Nat)
    (declared : ∀ node ∈ selected, Declaration root ty node)
    (n m : UInt64) (referenceCount : n.toNat = selected.length)
    (valueCount : m.toNat = (selected.map extent).sum) : n = 0 ∧ m = 0 := by
  have empty := absent.selection_empty selected declared
  subst selected
  constructor
  · exact UInt64.toNat_inj.mp referenceCount
  · exact UInt64.toNat_inj.mp valueCount

/-- Metadata and count consistency derive the successful branch of the
actual accessor. Pointer/lifecycle issuance rules remain importer obligations;
the proved raw call also covers defensive arguments outside those rules. -/
theorem QuietContract.selection_call [CInterface] {E : Type} {program : Program E}
    (contract : QuietContract ty write program)
    (absent : Absent root ty) (selected : List XML.Element) (extent : XML.Element → Nat)
    (declared : ∀ node ∈ selected, Declaration root ty node)
    (n m : UInt64) (referenceCount : n.toNat = selected.length)
    (valueCount : m.toNat = (selected.map extent).sum)
    (heap : Heap) (p : Address) (references sizes values : Option Address)
    (kind : Kind) (mode : Mode)
    (kindStored : load heap (p.member "kind") = some (.integer kind.code))
    (modeStored : load heap (p.member "mode") = some (.integer mode.code)) :
    ∀ observed, (machine program).Behaves
      (.calling (signature ty write).name
        (arguments ty.hasSizes (some p) references sizes values n m) heap .done) observed ↔
      observed = .terminates [] ⟨.integer 0, heap⟩ := by
  obtain ⟨rfl, rfl⟩ := selected_cardinalities_zero absent selected extent declared n m referenceCount valueCount
  exact contract.empty heap p references sizes values kind mode kindStored modeStored

end Rumoca.FMI3.AbsentVariables
