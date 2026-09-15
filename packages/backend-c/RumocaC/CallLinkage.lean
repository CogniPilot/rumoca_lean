import RumocaC.CallPolicyExecution

/-! Construct foreign bindings without shadowing existing definitions or imports; preserve the imported-address policy. -/
noncomputable section
namespace Rumoca.CCalls.Events.Linkage
open CTree CMemory
variable [CInterface] {E : Type}

/-- Extend the foreign table without shadowing a generated or imported name. -/
def withExternal (program : Program E) (external : External E)
    (internalFree : program.internal.definitions external.signature.name = none)
    (_externalFree : program.externals external.signature.name = none) : Program E where
  internal := program.internal
  addresses := program.addresses
  externals name := if name = external.signature.name then some external else program.externals name
  disjoint := by
    intro name fn found
    by_cases same : name = external.signature.name
    · simpa only [same] using internalFree
    · exact program.disjoint name fn (by simpa only [if_neg same] using found)
  names := by
    intro name fn found
    by_cases same : name = external.signature.name
    · simp only [if_pos same, Option.some.injEq] at found
      cases found
      exact same.symm
    · exact program.names name fn (by simpa only [if_neg same] using found)

theorem withExternal_bound (program : Program E) (external : External E)
    (internalFree : program.internal.definitions external.signature.name = none)
    (externalFree : program.externals external.signature.name = none) :
    (withExternal program external internalFree externalFree).externals external.signature.name =
      some external := by simp [withExternal]

theorem withExternal_keeps (program : Program E) (external : External E)
    (internalFree : program.internal.definitions external.signature.name = none)
    (externalFree : program.externals external.signature.name = none)
    (found : program.externals name = some fn) :
    (withExternal program external internalFree externalFree).externals name = some fn := by
  have different : name ≠ external.signature.name := by
    intro same
    rw [same, externalFree] at found
    contradiction
  simpa only [withExternal, if_neg different] using found

theorem withExternal_foreign (program : Program E) (external : External E)
    (internalFree : program.internal.definitions external.signature.name = none)
    (externalFree : program.externals external.signature.name = none)
    (foreign : CCallPolicy.ForeignAddresses program) :
    CCallPolicy.ForeignAddresses
      (withExternal program external internalFree externalFree) := foreign

/-- Bind a fresh function address only to an existing foreign entry. -/
def withAddress (program : Program E) (address : Address) (name : String)
    (_available : program.addresses address = none)
    (_external : ∃ fn, program.externals name = some fn) : Program E :=
  { program with addresses := fun p => if p = address then some name else program.addresses p }

theorem withAddress_foreign (program : Program E) (address : Address) (name : String)
    (available : program.addresses address = none)
    (external : ∃ fn, program.externals name = some fn)
    (foreign : CCallPolicy.ForeignAddresses program) :
    CCallPolicy.ForeignAddresses
      (withAddress program address name available external) := by
  intro p target found
  by_cases same : p = address
  · simp only [withAddress, if_pos same, Option.some.injEq] at found
    obtain ⟨fn, defined⟩ := external
    rw [← found]
    exact program.disjoint name fn defined
  · exact foreign p target (by simpa only [withAddress, if_neg same] using found)

end Rumoca.CCalls.Events.Linkage
