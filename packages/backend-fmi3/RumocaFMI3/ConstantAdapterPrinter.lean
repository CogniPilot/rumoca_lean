import RumocaFMI3.ConstantFunctions
import RumocaFMI3.AdapterFunctionsPrinter
import RumocaFMI3.StaticFactoryPrinter
import RumocaFMI3.RuntimePrinter
import RumocaC.FunctionSequence

/-! Complete function-section grammar for the constant-rate FMI adapter renderer,
the constant instance of the profile-generic `AdapterFunctionsPrinter`. The section
following the fixed constant declaration preamble tokenizes maximally as the
constant function list, using each dispatched constant body's proved printability
and the shared helper/scalar-body printability. The reserved-record factory
printability and the section-tokenization contract are the profile-generic ones
instantiated at the constant preamble and list; only the per-signature
dispatched-body printability is constant-specific. The preamble still requires
separate header/directive interpretation, exactly as the scalar boundary does. -/
namespace Rumoca.FMI3.ConstantAdapterPrinter
open CTree CTree.Printer CTree.Syntax
set_option autoImplicit false
variable {source : AST.Model} {n : Nat}

/-- Every dispatched constant function is printable: the constant-specific bodies
(the Float64 accessors, the constant derivative getter and the constant
`fmi3DoStep`) use their proved printability, the profile-independent tensor bodies
use theirs at the constant state shape, and every other signature uses the scalar
body printability under a printable signature. -/
theorem constantFunction_printable (model : Solve.FMI3Model source)
    (m : Solve.ConstantFMI3Model n) (sig : Signature)
    (valid : SignaturePrintable RuntimePrinter.typedefs sig) :
    FunctionPrintable RuntimePrinter.typedefs (ConstantFunctions.constantFunction model m sig) := by
  -- The emitted function carries the header prototype `sig`, so its signature is
  -- printable by `valid`; its body is the dispatched constant (or tensor, or scalar) body.
  refine ⟨valid, ?_⟩
  show ∀ stmt ∈ (ConstantFunctions.constantDispatch model m sig).body,
    ItemPrintable RuntimePrinter.typedefs stmt
  unfold ConstantFunctions.constantDispatch
  split <;>
    first
      | exact TensorReset.body_printable m.shape
      | exact TensorNominals.body_printable m.shape
      | exact TensorCountQueries.body_printable m.shape false
      | exact TensorCountQueries.body_printable m.shape true
      | exact TensorSetTime.body_printable
      | exact TensorLifecycleModes.body_printable .enterInitialization
      | exact TensorLifecycleModes.body_printable .exitInitialization
      | exact TensorLifecycleModes.body_printable .enterEvent
      | exact TensorLifecycleModes.body_printable .enterContinuous
      | exact TensorLifecycleModes.body_printable .terminate
      | exact StaticFactory.Printer.release_printable.2
      | exact (AdapterFunctionsPrinter.factory_printable model m.shape .me (TensorMetadata.constantToken m.name)).2
      | exact (AdapterFunctionsPrinter.factory_printable model m.shape .cs (TensorMetadata.constantToken m.name)).2
      | exact ConstantFloat64.getBody_printable m.shape
      | exact ConstantFloat64.setBody_printable m.shape
      | exact TensorContinuousStates.getBody_printable m.shape
      | exact TensorContinuousStates.setBody_printable m.shape
      | exact ConstantDerivative.derivBody_printable m.shape
      | exact ConstantDoStep.body_printable
      | exact (RuntimePrinter.function_printable model sig valid).2

/-- Every function of the constant adapter list is printable, given the shared
helper printability and per-signature printability. -/
theorem functions_printable (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (signatures : List Signature)
    (valid : ∀ sig ∈ signatures, SignaturePrintable RuntimePrinter.typedefs sig) :
    ∀ fn ∈ ConstantFunctions.functions model m signatures, FunctionPrintable RuntimePrinter.typedefs fn := by
  intro fn member
  rcases List.mem_append.mp member with helper | exported
  · exact RuntimePrinter.helpers_printable fn (ConstantFunctions.helpers_subset fn helper)
  · obtain ⟨sig, sigMember, rfl⟩ := List.mem_map.mp exported
    exact constantFunction_printable model m sig (valid sig sigMember)

/-- Independent normal-context tokenization and per-function grammar for the
entire section following the fixed constant declaration preamble: the
profile-generic `FunctionsContract` at the constant preamble and list. -/
abbrev FunctionsContract (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (signatures : List Signature) (adapter : String) : Prop :=
  AdapterFunctionsPrinter.FunctionsContract
    (functionPrefix m.name ++ "#include \"model.c\"\n" ++
      ConstantFunctions.declarations m.shape (ConstantFunctions.rates m))
    (ConstantFunctions.functions model m signatures) adapter

/-- The constant renderer's function section tokenizes maximally as the constant
function list, the constant instance of `AdapterFunctionsPrinter.functionsContract_of`. -/
theorem rendered_contract (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (signatures : List Signature)
    (valid : ∀ sig ∈ signatures, SignaturePrintable RuntimePrinter.typedefs sig) :
    FunctionsContract model m signatures (ConstantFunctions.render model m signatures) :=
  AdapterFunctionsPrinter.functionsContract_of
    (functionPrefix m.name ++ "#include \"model.c\"\n" ++
      ConstantFunctions.declarations m.shape (ConstantFunctions.rates m))
    (ConstantFunctions.functions model m signatures)
    (ConstantFunctions.render model m signatures)
    (ConstantFunctions.rendered_functions model m signatures)
    (functions_printable model m signatures valid)

end Rumoca.FMI3.ConstantAdapterPrinter
