import RumocaFMI3.TensorFunctions
import RumocaFMI3.StaticFactoryPrinter
import RumocaFMI3.RuntimePrinter
import RumocaC.FunctionSequence

/-! Complete function-section grammar for the tensor FMI adapter renderer, the
tensor analog of `AdapterPrinter`. The section following the fixed tensor
declaration preamble tokenizes maximally as the tensor function list, using each
dispatched tensor body's proved printability and the shared helper/scalar-body
printability. The preamble still requires separate header/directive
interpretation, exactly as the scalar boundary does. -/
namespace Rumoca.FMI3.TensorAdapterPrinter
open CTree CTree.Printer CTree.Syntax
set_option autoImplicit false
variable {source : AST.Model} {shape : Rumoca.Tensor.Shape}

private theorem named_type (name : String) (member : name ∈ RuntimePrinter.typedefs) :
    TypeSpelling RuntimePrinter.typedefs name := by
  have valid : RuntimePrinter.typedefs.all (CIdentifier.valid []) = true := by decide +kernel
  exact .named (.typedefName member (List.all_eq_true.mp valid name member))

/-- The tensor public factory function is printable: the shared admission prefix
followed by the tensor reserved-record initializer (slot store, lifecycle
metadata, the counted state-region zero fill and the handle return). This is the
one dispatched tensor body without an existing printability theorem. -/
theorem factory_printable (model : Solve.FMI3Model source) (shape : Rumoca.Tensor.Shape) (kind : Kind)
    (tok : String := token model) :
    FunctionPrintable RuntimePrinter.typedefs (TensorFactory.function model shape kind tok) := by
  refine ⟨StaticFactory.Printer.signature_printable kind, ?_⟩
  have iType : TypeSpelling RuntimePrinter.typedefs "Instance *" :=
    .pointer (text := "Instance") (named_type _ (by decide +kernel))
  have fType : TypeSpelling RuntimePrinter.typedefs "fmi3Float64 *" :=
    .pointer (text := "fmi3Float64") (named_type _ (by decide +kernel))
  have sType : TypeSpelling RuntimePrinter.typedefs "size_t" := named_type _ (by decide +kernel)
  cases kind <;>
    simp only [TensorFactory.function, FactoryPrefix.body, FactoryPrefix.entry,
      FactoryPrefix.validation, FactoryPrefix.identityGuard, FactoryPrefix.capabilityGuard,
      FactoryRejection.code, FactoryRejection.logCall, TensorFactory.code, StaticFactory.reserve,
      StaticFactory.guard, StaticFactory.exhausted, TensorFactory.initializeInstance,
      StaticFactory.selectInstance, InstanceSlot.code, InstanceSlot.statement,
      TensorInstanceInit.code, TensorInstanceInit.slotStore, TensorInstanceInit.metaCode,
      TensorInstanceInit.stateTail, TensorReset.zeroBody, TensorFloat64.dstCell,
      InstanceInitialization.returnHandle, TensorInstance.stateName, CAtomicScan.function,
      Identity.function, Runtime.region, Runtime.put, Runtime.field, Runtime.v, Runtime.n, Runtime.mode,
      Runtime.ret, Runtime.call, CLoops.loop, CLoops.counterStep,
      List.foldr_cons, List.foldr_nil, List.map_cons, List.mem_cons,
      List.not_mem_nil, or_false, or_imp, forall_and, List.cons_append, List.nil_append,
      forall_eq] <;>
    repeat first
      | exact CNull.literal_printable _
      | exact iType
      | exact fType
      | exact sType
      | exact named_type _ (by decide +kernel)
      | exact (TypeSpelling.named (.primitive (by decide +kernel)) : TypeSpelling RuntimePrinter.typedefs "double")
      | apply And.intro
      | apply ItemPrintable.declare
      | apply ItemPrintable.assign
      | apply ItemPrintable.branch
      | apply ItemPrintable.eval
      | apply ItemPrintable.whileLoop
      | apply ItemPrintable.returnValue
      | apply Printable.dereference
      | apply Printable.cast
      | apply Printable.binary
      | apply Printable.not
      | apply Printable.address
      | apply Printable.call
      | apply Printable.field
      | apply Printable.index
      | exact Printable.natural
      | exact Printable.string
      | apply Printable.identifier
      | solve | intro stmt impossible; cases impossible
      | decide +kernel
      | simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
          Postfix, FieldBase]

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
entire section following the fixed tensor declaration preamble. -/
def FunctionsContract (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature) (adapter : String) : Prop :=
  ∃ text, adapter = (functionPrefix m.name ++ "#include \"model.c\"\n" ++
      TensorStorage.declarations shape m.hasOutput) ++ text ∧
    FunctionsTokenization RuntimePrinter.typedefs text (TensorFunctions.functions model m signatures)

/-- The tensor renderer's function section tokenizes maximally as the tensor
function list, the tensor analog of `AdapterPrinter.rendered_contract`. -/
theorem rendered_contract (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature)
    (valid : ∀ sig ∈ signatures, SignaturePrintable RuntimePrinter.typedefs sig) :
    FunctionsContract model m signatures (TensorFunctions.render model m signatures) :=
  ⟨String.join ((TensorFunctions.functions model m signatures).map Function.render),
    TensorFunctions.rendered_functions model m signatures,
    function_sequence_tokenization (functions_printable model m signatures valid)⟩

end Rumoca.FMI3.TensorAdapterPrinter
