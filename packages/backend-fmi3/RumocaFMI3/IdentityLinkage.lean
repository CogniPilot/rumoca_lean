import RumocaFMI3.IdentityCalls
import RumocaFMI3.LiteralPreparation
import RumocaC.StringBindings

/-! Bind the identity validator to the actual emitted function table. The
artifact checker checks external-name freshness from its quoted signatures.
This constructs a consistent authored library environment; native library
and header interpretation remain separate correspondence obligations. -/
noncomputable section
namespace Rumoca.FMI3.Identity
open CTree CMemory

def LibraryNamesFresh (signatures : List Signature) : Prop :=
  ∀ sig ∈ signatures, sig.name ∉ CStringCalls.routineNames

theorem library_undefined (model : Solve.FMI3Model source) (signatures : List Signature)
    (fresh : LibraryNamesFresh signatures) (name : String) (member : name ∈ CStringCalls.routineNames) :
    (LiteralPreparation.program model signatures).definitions name = none := by
  have missing : (LiteralPreparation.functions model signatures).find?
      (fun fn => fn.signature.name == name) = none := by
    apply List.find?_eq_none.mpr
    intro fn belongs
    simp only [LiteralPreparation.functions, List.mem_append, List.mem_map] at belongs
    rcases belongs with helper | ⟨sig, belongs, rfl⟩
    · simp only [Runtime.helpers, List.mem_cons, List.not_mem_nil, or_false] at helper
      simp only [CStringCalls.routineNames, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases helper with rfl | rfl | rfl | rfl <;>
        rcases member with rfl | rfl | rfl <;> decide +kernel
    · have different : sig.name ≠ name := fun same => fresh sig belongs (same ▸ member)
      simpa only [Runtime.function, beq_iff_eq] using different
  simp only [LiteralPreparation.program, missing]
  simp only [CStringCalls.routineNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> rfl

theorem helper_defined (model : Solve.FMI3Model source) (sigs : List Signature) :
    (LiteralPreparation.program model sigs).definitions function.signature.name = some (.tree function) :=
  LiteralPreparation.helpers_bound model sigs function (by simp [Runtime.helpers])

/-- The actual table admits these external contracts for every static-literal
address map. No successful execution or native result is a premise. -/
theorem bindings_exist (model : Solve.FMI3Model source) (sigs : List Signature)
    (fresh : LibraryNamesFresh sigs) (literals : CLiteralAddresses) (E : Type) :
    ∃ program : @CCalls.Events.Program (cInterface literals) E,
      @CCalls.Events.Program.internal (cInterface literals) E program =
        LiteralPreparation.program model sigs ∧
      Bindings (interface := cInterface literals) program := by
  letI : CInterface := cInterface literals
  let program : CCalls.Events.Program E := CStringCalls.linked
    (LiteralPreparation.program model sigs) (library_undefined model sigs fresh)
    (by rfl) (by rfl) (fun _ => none)
  refine ⟨program, rfl, ?_⟩
  constructor <;> rfl

end Rumoca.FMI3.Identity
