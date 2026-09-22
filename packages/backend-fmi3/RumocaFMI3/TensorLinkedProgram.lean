import RumocaFMI3.TensorFunctions
import RumocaFMI3.PublicAPI
import RumocaC.TreeTable
import RumocaC.TensorSquareTable

/-! Tensor adapter assembly with an explicit numerical function list.

The generic API uses the supplied trees verbatim. It neither selects numerical
computations nor imports the compiler. The square wrappers consume the table
owned by backend-c and derive name separation from existing public coverage.
These are definition-table facts; source/byte identity, event-program linkage
and execution contracts must be composed by their respective owners.

The inherited Program.kernel field is populated for API compatibility, but no
definition lookup can select a kernel tag from this tree-only assembly. -/
namespace Rumoca.FMI3.TensorFunctions
open CTree CCalls.TreeTable
set_option autoImplicit false
variable {source : AST.Model} {shape : Tensor.Shape}

/-- Concatenation preserves unique names when both lists are unique and their
name sets are disjoint. No ordering or membership premise is discarded. -/
theorem append_unique (before numerical : List Function)
    (beforeUnique : (before.map (fun fn => fn.signature.name)).Nodup)
    (numericalUnique : (numerical.map (fun fn => fn.signature.name)).Nodup)
    (separate : ∀ name ∈ before.map (fun fn => fn.signature.name),
      name ∉ numerical.map (fun fn => fn.signature.name)) :
    ((before ++ numerical).map (fun fn => fn.signature.name)).Nodup := by
  rw [List.map_append, List.nodup_append]
  refine ⟨beforeUnique, numericalUnique, ?_⟩
  intro name left other right equal
  subst other
  exact separate name left right

/-- Assemble the adapter and explicitly supplied numerical trees. The list
argument is required even when a caller uses the current square profile. -/
def linkedProgram (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature) (numerical : List Function) : CCalls.Program :=
  treeProgram (functions model m signatures ++ numerical)
    (CSyntax.fromTarget (C.lower model.solve))

theorem linked_numerical (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature) (numerical : List Function)
    (unique : ((functions model m signatures ++ numerical).map
      (fun fn => fn.signature.name)).Nodup) :
    CCalls.Typed.Extends (treeDefinitions numerical) (linkedProgram model m signatures numerical) :=
  extends_append _ _ _ unique

theorem linked_adapter (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature) (numerical : List Function)
    (unique : ((functions model m signatures ++ numerical).map
      (fun fn => fn.signature.name)).Nodup)
    (fn : Function) (member : fn ∈ functions model m signatures) :
    (linkedProgram model m signatures numerical).definitions fn.signature.name = some (.tree fn) :=
  program_lookup_member _ _ _ unique (List.mem_append_left _ member)

theorem linked_no_kernel (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature) (numerical : List Function) (name : String)
    (fn : CStatements.Function) :
    (linkedProgram model m signatures numerical).definitions name ≠ some (.kernel fn) :=
  no_kernel _ _ _ _

/-- Current square-profile assembly. The table comes from backend-c; this
wrapper makes no claim that it implements an arbitrary supplied model's IVP. -/
def squareLinkedProgram (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature) : CCalls.Program :=
  linkedProgram model m signatures TensorKernel.functions

theorem public_kernel_separate (api : PublicAPI.Entry) :
    api.signature.name ∉ TensorKernel.functions.map (fun fn => fn.signature.name) := by
  have capabilities : ∀ sig ∈ CapabilityRejection.signatures,
      sig.name ∉ TensorKernel.functions.map (fun fn => fn.signature.name) := by decide +kernel
  cases api with
  | capability sig member => exact capabilities sig member
  | factory kind => cases kind <;> decide +kernel
  | initialization enter => cases enter <;> decide +kernel
  | counts events => cases events <;> decide +kernel
  | states write => cases write <;> decide +kernel
  | float64 write => cases write <;> decide +kernel
  | entry which => cases which <;> decide +kernel
  | absent ty write => cases ty <;> cases write <;> decide +kernel
  | _ => decide +kernel

theorem square_names_disjoint (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature) (covered : PublicAPI.Covered signatures) :
    ∀ name ∈ (functions model m signatures).map (fun fn => fn.signature.name),
      name ∉ TensorKernel.functions.map (fun fn => fn.signature.name) := by
  intro name left right
  rw [functions_names] at left
  rcases List.mem_append.mp left with helper | exported
  · have separated : ∀ name ∈ helpers.map (fun fn => fn.signature.name),
        name ∉ TensorKernel.functions.map (fun fn => fn.signature.name) := by decide +kernel
    exact separated name helper right
  · obtain ⟨sig, member, same⟩ := List.mem_map.mp exported
    obtain ⟨api, identified⟩ := covered sig member
    exact public_kernel_separate api (by simpa [identified, same] using right)

/-- Existing adapter uniqueness and public coverage derive combined uniqueness
for the square table; clients need not supply an additional collision premise. -/
theorem combined_unique (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature)
    (unique : ((functions model m signatures).map (fun fn => fn.signature.name)).Nodup)
    (covered : PublicAPI.Covered signatures) :
    ((functions model m signatures ++ TensorKernel.functions).map
      (fun fn => fn.signature.name)).Nodup :=
  append_unique _ _ unique TensorKernel.functions_unique
    (square_names_disjoint model m signatures covered)

theorem linked_numerical_covered (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature)
    (unique : ((functions model m signatures).map (fun fn => fn.signature.name)).Nodup)
    (covered : PublicAPI.Covered signatures) :
    CCalls.Typed.Extends TensorKernel.definitions (squareLinkedProgram model m signatures) :=
  linked_numerical model m signatures TensorKernel.functions
    (combined_unique model m signatures unique covered)

theorem square_linked_adapter (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature)
    (unique : ((functions model m signatures).map (fun fn => fn.signature.name)).Nodup)
    (covered : PublicAPI.Covered signatures)
    (fn : Function) (member : fn ∈ functions model m signatures) :
    (squareLinkedProgram model m signatures).definitions fn.signature.name = some (.tree fn) :=
  linked_adapter model m signatures TensorKernel.functions
    (combined_unique model m signatures unique covered) fn member

theorem square_linked_no_kernel (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature) (name : String) (fn : CStatements.Function) :
    (squareLinkedProgram model m signatures).definitions name ≠ some (.kernel fn) :=
  linked_no_kernel model m signatures TensorKernel.functions name fn

end Rumoca.FMI3.TensorFunctions
