import RumocaFMI3.TensorFunctions
import RumocaFMI3.AdapterFunctionsPrinter
import RumocaFMI3.StaticFactoryPrinter
import RumocaFMI3.RuntimePrinter
import RumocaC.FunctionSequence

/-! Complete function-section grammar for the tensor FMI adapter renderer, the
tensor instance of the profile-generic `AdapterFunctionsPrinter`. The section
following the fixed tensor declaration preamble tokenizes maximally as the tensor
function list, using each dispatched tensor body's proved printability and the
shared helper/scalar-body printability. The reserved-record factory printability
and the section-tokenization contract are the profile-generic ones instantiated at
the tensor preamble and list; only the per-signature dispatched-body printability
is tensor-specific. The preamble still requires separate header/directive
interpretation, exactly as the scalar boundary does. -/
namespace Rumoca.FMI3.TensorAdapterPrinter
open CTree CTree.Printer CTree.Syntax
set_option autoImplicit false
variable {source : AST.Model} {shape : Rumoca.Tensor.Shape}

/-- The tensor public factory function is printable: the profile-generic
reserved-record factory printability at the tensor state shape. -/
theorem factory_printable (model : Solve.FMI3Model source) (shape : Rumoca.Tensor.Shape) (kind : Kind)
    (tok : String := token model) :
    FunctionPrintable RuntimePrinter.typedefs (TensorFactory.function model shape kind tok) :=
  AdapterFunctionsPrinter.factory_printable model shape kind tok

/-- Every dispatched tensor function is printable: the 19 shape-dependent bodies
use their proved printability, and every other signature uses the scalar body
printability under a printable signature. -/
theorem tensorFunction_printable (model : Solve.FMI3Model source)
    (m : Solve.TensorFMI3Model shape) (sig : Signature)
    (valid : SignaturePrintable RuntimePrinter.typedefs sig) :
    FunctionPrintable RuntimePrinter.typedefs (TensorFunctions.tensorFunction model m sig) := by
  -- The emitted function carries the header prototype `sig`, so its signature is
  -- printable by `valid`; its body is the dispatched tensor (or scalar) body.
  refine ⟨valid, ?_⟩
  show ∀ stmt ∈ (TensorFunctions.tensorDispatch model m sig).body,
    ItemPrintable RuntimePrinter.typedefs stmt
  unfold TensorFunctions.tensorDispatch
  split <;>
    first
      | exact TensorReset.body_printable shape
      | exact TensorNominals.body_printable shape
      | exact TensorCountQueries.body_printable shape false
      | exact TensorCountQueries.body_printable shape true
      | exact TensorSetTime.body_printable
      | exact TensorLifecycleModes.body_printable .enterInitialization
      | exact TensorLifecycleModes.body_printable .exitInitialization
      | exact TensorLifecycleModes.body_printable .enterEvent
      | exact TensorLifecycleModes.body_printable .enterContinuous
      | exact TensorLifecycleModes.body_printable .terminate
      | exact StaticFactory.Printer.release_printable.2
      | exact (factory_printable model shape .me (TensorMetadata.token m)).2
      | exact (factory_printable model shape .cs (TensorMetadata.token m)).2
      | exact TensorFloat64.getBody_printable shape (TensorFunctions.outputShape m)
      | exact TensorFloat64.setBody_printable shape
      | exact TensorContinuousStates.getBody_printable shape
      | exact TensorContinuousStates.setBody_printable shape
      | exact TensorContinuousStates.derivBody_printable shape m.hasOutput
      | exact TensorDoStep.body_printable shape m.hasOutput
      | exact (RuntimePrinter.function_printable model sig valid).2

/-- Every function of the tensor adapter list is printable, given the shared
helper printability and per-signature printability. -/
theorem functions_printable (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature)
    (valid : ∀ sig ∈ signatures, SignaturePrintable RuntimePrinter.typedefs sig) :
    ∀ fn ∈ TensorFunctions.functions model m signatures, FunctionPrintable RuntimePrinter.typedefs fn := by
  intro fn member
  rcases List.mem_append.mp member with helper | exported
  · exact RuntimePrinter.helpers_printable fn (TensorFunctions.helpers_subset fn helper)
  · obtain ⟨sig, sigMember, rfl⟩ := List.mem_map.mp exported
    exact tensorFunction_printable model m sig (valid sig sigMember)

/-- Independent normal-context tokenization and per-function grammar for the
entire section following the fixed tensor declaration preamble: the profile-generic
`FunctionsContract` at the tensor preamble and list. -/
abbrev FunctionsContract (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature) (adapter : String) : Prop :=
  AdapterFunctionsPrinter.FunctionsContract
    (functionPrefix m.name ++ "#include \"model.c\"\n" ++ TensorStorage.declarations shape m.hasOutput)
    (TensorFunctions.functions model m signatures) adapter

/-- The tensor renderer's function section tokenizes maximally as the tensor
function list, the tensor instance of `AdapterFunctionsPrinter.functionsContract_of`. -/
theorem rendered_contract (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature)
    (valid : ∀ sig ∈ signatures, SignaturePrintable RuntimePrinter.typedefs sig) :
    FunctionsContract model m signatures (TensorFunctions.render model m signatures) :=
  AdapterFunctionsPrinter.functionsContract_of
    (functionPrefix m.name ++ "#include \"model.c\"\n" ++ TensorStorage.declarations shape m.hasOutput)
    (TensorFunctions.functions model m signatures)
    (TensorFunctions.render model m signatures)
    (TensorFunctions.rendered_functions model m signatures)
    (functions_printable model m signatures valid)

end Rumoca.FMI3.TensorAdapterPrinter
