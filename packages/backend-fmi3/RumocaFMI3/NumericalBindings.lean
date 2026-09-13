import RumocaFMI3.LiteralPreparation
import RumocaC.Statements

/-! Numerical-name linkage for the actual prepared definition table.
The fixed artifact checker must establish freshness from its quoted signatures
when a numerical public-call contract is integrated. -/
namespace Rumoca.FMI3.LiteralPreparation
open CTree

def kernelName : Profile.Function → String
  | .rhs => "rumoca_rhs"
  | .step => "rumoca_step"
  | .sample => "rumoca_sample"

def KernelNamesFresh (signatures : List Signature) : Prop :=
  ∀ sig ∈ signatures, ∀ function, sig.name ≠ kernelName function

theorem numerical_bound (model : Solve.FMI3Model source) (signatures : List Signature)
    (fresh : KernelNamesFresh signatures) (function : Profile.Function) :
    (program model signatures).definitions (kernelName function) = some (.kernel function) := by
  have missing : (functions model signatures).find?
      (fun fn => fn.signature.name == kernelName function) = none := by
    apply List.find?_eq_none.mpr
    intro fn member
    simp only [functions, List.mem_append, List.mem_map] at member
    rcases member with helper | ⟨sig, member, rfl⟩
    · simp only [Runtime.helpers, List.mem_cons, List.not_mem_nil, or_false] at helper
      rcases helper with rfl | rfl | rfl | rfl <;> cases function <;> decide +kernel
    · simpa only [Runtime.function, beq_iff_eq] using fresh sig member function
  simp only [program, missing]
  cases function <;> rfl

theorem numerical_program (model : Solve.FMI3Model source) (signatures : List Signature) :
    (program model signatures).kernel = CExecution.program model.solve := rfl

end Rumoca.FMI3.LiteralPreparation
