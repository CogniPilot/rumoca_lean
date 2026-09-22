import RumocaEFMI.TensorProductionProofs
import RumocaEFMI.CInterface
import RumocaC.TreeTable
import RumocaC.TensorProgramCalls

/-! Exact tensor eFMI numerical tree linkage with the actual backend type
bindings. Public-method execution is composed by downstream contracts. -/
namespace Rumoca.EFMI.TensorNumericalLinkage
open CTree CMemory CTensor CTensor.Lowering Solve.Tensor CCalls.TreeTable
open CTensor.ProgramFixture

/-- The seven printed trees, in existing dependency order. No coefficient entry. -/
def numericalFunctions : List Function :=
  [Fill.function, CTensor.function .add, CTensor.function .mul, Diagonal.function,
   (IVPEntry.plan ArrayProfile.stateShape).initial.function.tree,
   (IVPEntry.plan ArrayProfile.stateShape).derivative.function.tree,
   SquareDiagonal.function]

theorem numerical_count : numericalFunctions.length = 7 := rfl

theorem pieces_exact :
    TensorProduction.kernelPieces =
      "#include <stddef.h>\n#include <stdint.h>\n" ::
        numericalFunctions.map Function.render := rfl

theorem text_exact :
    TensorProduction.kernelText =
      "#include <stddef.h>\n#include <stdint.h>\n" ++
        String.join (numericalFunctions.map Function.render) := rfl

theorem production_exact :
    TensorProduction.render =
      "#include <stddef.h>\n#include <stdint.h>\n" ++
        String.join (numericalFunctions.map Function.render) ++
        TensorProduction.header ++
        String.join (TensorProduction.functions.map Function.render) := rfl

theorem numerical_names :
    numericalFunctions.map (fun f => f.signature.name) =
      ["rumoca_tensor_fill", "rumoca_tensor_add", "rumoca_tensor_mul",
       "rumoca_tensor_diagonal", "rumoca_initialize", "rumoca_rhs",
       "rumoca_square_jacobian_diag"] := rfl

theorem numerical_unique :
    (numericalFunctions.map (fun f => f.signature.name)).Nodup := by
  rw [numerical_names]
  decide +kernel

def definitions : CLoops.Calls.Definitions := treeDefinitions numericalFunctions

theorem defined_member (fn : Function) (member : fn ∈ numericalFunctions) :
    definitions fn.signature.name = some fn :=
  lookup_member numericalFunctions fn numerical_unique member

theorem fill_defined : definitions Fill.function.signature.name = some Fill.function :=
  defined_member _ (by simp [numericalFunctions])

theorem binary_defined (op : Tensor.BinaryOp) (used : op = .add ∨ op = .mul) :
    definitions (CTensor.function op).signature.name = some (CTensor.function op) := by
  rcases used with rfl | rfl
  all_goals exact defined_member _ (by simp [numericalFunctions])

theorem diagonal_defined :
    definitions Diagonal.function.signature.name = some Diagonal.function :=
  defined_member _ (by simp [numericalFunctions])

theorem initial_defined (shape : Tensor.Shape) :
    definitions (IVPEntry.plan shape).initial.function.name =
      some (IVPEntry.plan shape).initial.function.tree := by
  exact defined_member (IVPEntry.plan shape).initial.function.tree (by
    change (IVPEntry.plan ArrayProfile.stateShape).initial.function.tree ∈ numericalFunctions
    simp [numericalFunctions])

theorem derivative_defined (shape : Tensor.Shape) :
    definitions (IVPEntry.plan shape).derivative.function.name =
      some (IVPEntry.plan shape).derivative.function.tree := by
  exact defined_member (IVPEntry.plan shape).derivative.function.tree (by
    change (IVPEntry.plan ArrayProfile.stateShape).derivative.function.tree ∈ numericalFunctions
    simp [numericalFunctions])

theorem square_diagonal_defined :
    definitions SquareDiagonal.function.signature.name = some SquareDiagonal.function :=
  defined_member _ (by simp [numericalFunctions])

/-- Explicitly exclude the two unprinted binary helpers and both coefficient entries. -/
theorem absent_unprinted :
    definitions "rumoca_tensor_sub" = none ∧ definitions "rumoca_tensor_div" = none ∧
    definitions "rumoca_square_jacobian" = none ∧
    definitions "rumoca_square_jacobian_coefficients" = none := by
  decide +kernel

/-- A tree-only program leaves the required kernel slot arbitrary and unused by lookup. -/
def numericalProgram (unusedKernel : CSyntax.Program) : CCalls.Program :=
  treeProgram numericalFunctions unusedKernel

theorem numerical_tree_bound (unusedKernel : CSyntax.Program) (fn : Function)
    (member : fn ∈ numericalFunctions) :
    (numericalProgram unusedKernel).definitions fn.signature.name = some (.tree fn) :=
  program_lookup_member numericalFunctions unusedKernel fn numerical_unique member

theorem numerical_extends (unusedKernel : CSyntax.Program) :
    CCalls.Typed.Extends definitions (numericalProgram unusedKernel) := by
  intro name fn found
  exact (program_lookup_iff numericalFunctions unusedKernel name fn).2 found

/-- Same ordered numerical prefix plus the three actual emitted method trees. -/
def allFunctions : List Function := numericalFunctions ++ TensorProduction.functions

theorem all_count : allFunctions.length = 10 := rfl

theorem all_unique : (allFunctions.map (fun f => f.signature.name)).Nodup := by
  decide +kernel

def program (unusedKernel : CSyntax.Program) : CCalls.Program :=
  treeProgram allFunctions unusedKernel

theorem actual_member (unusedKernel : CSyntax.Program) (fn : Function)
    (member : fn ∈ allFunctions) :
    (program unusedKernel).definitions fn.signature.name = some (.tree fn) :=
  program_lookup_member allFunctions unusedKernel fn all_unique member

theorem numerical_in_actual (unusedKernel : CSyntax.Program) :
    CCalls.Typed.Extends definitions (program unusedKernel) := by
  intro name fn found
  obtain ⟨member, named⟩ := lookup_some numericalFunctions name fn found
  have result := actual_member unusedKernel fn (List.mem_append_left _ member)
  simpa only [named] using result

theorem method_defined (unusedKernel : CSyntax.Program) (fn : Function)
    (member : fn ∈ TensorProduction.functions) :
    (program unusedKernel).definitions fn.signature.name = some (.tree fn) :=
  actual_member unusedKernel fn (List.mem_append_right _ member)

theorem no_kernel_tag (unusedKernel : CSyntax.Program) (name : String)
    (fn : CStatements.Function) :
    (program unusedKernel).definitions name ≠ some (.kernel fn) :=
  no_kernel allFunctions unusedKernel name fn

/-- Connect the backend's profile-indexed model to the reusable C plan's actual IR. -/
theorem prepared_kernel (shape : Tensor.Shape) (model : EFMI.TensorModel shape) :
    model.kernel = IVPEntry.kernel shape :=
  model.profile.trans rfl

theorem initial_shape_bytes (shape : Tensor.Shape) :
    (IVPEntry.plan shape).initial.function.tree.render = IVPEntry.sources.initial := rfl

theorem derivative_shape_bytes (shape : Tensor.Shape) :
    (IVPEntry.plan shape).derivative.function.tree.render = IVPEntry.sources.derivative := rfl

theorem initial_required (shape : Tensor.Shape) :
    requiredOps (IVPEntry.kernel shape).initialProgram = [] := rfl

theorem derivative_required (shape : Tensor.Shape) :
    requiredOps (IVPEntry.kernel shape).derivative = [.mul] := rfl

/-! The actual backend dictionary interprets every emitted numerical spelling. -/
namespace NumericalInterface

abbrev types := EFMI.cTypes
abbrev interface : CInterface := EFMI.cInterface

theorem types_existing (name : String) (type : CType)
    (old : EFMI.cTypes name = some type) : types name = some type := old

theorem constants_unchanged : interface.constants = EFMI.cInterface.constants := rfl
theorem literals_unchanged : interface.literals = EFMI.cInterface.literals := rfl
theorem binary_header : CTensor.HeaderTypes interface := ⟨rfl, rfl, rfl⟩
theorem fill_header : Fill.HeaderTypes interface := ⟨rfl, rfl, rfl⟩

end NumericalInterface

section
variable [interface : CInterface]

/-- Current field evaluation loads the field cell; it does not by itself supply
the array-member pointer needed by the emitted numerical call. -/
theorem selfField_eval (env : CBody.Locals) (heap : Heap) (self : Address) (name : String)
    (bound : env "self" = some (.pointer (some self))) :
    CBody.eval env heap (TensorProduction.selfField name) = load heap (self.member name) := by
  simp [TensorProduction.selfField, CBody.eval, CBody.evalWith, CBody.resolve, bound, Value.address,
    CDeclaredMembers.memberValue, CDeclaredMembers.arrayAt, CDeclaredMembers.fieldAt]

theorem selfField_missing (env : CBody.Locals) (heap : Heap) (self : Address) (name : String)
    (bound : env "self" = some (.pointer (some self)))
    (missing : load heap (self.member name) = none) :
    CBody.eval env heap (TensorProduction.selfField name) = none :=
  (selfField_eval env heap self name bound).trans missing

/-- Only instruction-selected binary helpers, plus existing unconditional fill/header needs. -/
theorem library_for (p : Program Γ shape)
    (used : ∀ op ∈ requiredOps p, op = .add ∨ op = .mul)
    (binaryHeader : CTensor.HeaderTypes interface) (fillHeader : Fill.HeaderTypes interface) :
    LibraryFor p definitions :=
  ⟨binaryHeader, fillHeader, fun op member => binary_defined op (used op member), fill_defined⟩

theorem initial_library (shape : Tensor.Shape)
    (binaryHeader : CTensor.HeaderTypes interface) (fillHeader : Fill.HeaderTypes interface) :
    LibraryFor (IVPEntry.kernel shape).initialProgram definitions :=
  library_for _ (by intro op used; simp [initial_required] at used) binaryHeader fillHeader

theorem derivative_library (shape : Tensor.Shape)
    (binaryHeader : CTensor.HeaderTypes interface) (fillHeader : Fill.HeaderTypes interface) :
    LibraryFor (IVPEntry.kernel shape).derivative definitions := by
  apply library_for _ ?_ binaryHeader fillHeader
  intro op used
  exact Or.inr (by simpa [derivative_required] using used)

end

theorem initial_library_numerical (shape : Tensor.Shape) :
    letI : CInterface := NumericalInterface.interface
    LibraryFor (IVPEntry.kernel shape).initialProgram definitions := by
  letI : CInterface := NumericalInterface.interface
  exact initial_library shape NumericalInterface.binary_header NumericalInterface.fill_header

theorem derivative_library_numerical (shape : Tensor.Shape) :
    letI : CInterface := NumericalInterface.interface
    LibraryFor (IVPEntry.kernel shape).derivative definitions := by
  letI : CInterface := NumericalInterface.interface
  exact derivative_library shape NumericalInterface.binary_header NumericalInterface.fill_header

end Rumoca.EFMI.TensorNumericalLinkage
