import RumocaFMI3.TensorFunctions
import RumocaFMI3.StaticFactoryPrinter
import RumocaFMI3.RuntimePrinter
import RumocaC.FunctionSequence

/-! Profile-generic function-section grammar for an FMI adapter renderer.

Every FMI 3 adapter profile emits the same function-section shape: a fixed
declaration preamble followed by the concatenated helper and dispatched-function
renderings, which tokenizes maximally as the emitted function list. The reserved-
record public factory body is identical across profiles (the shared admission
prefix followed by the reserved-record initializer over the state region), so its
printability is proved once here (`factory_printable`). The section-tokenization
contract (`FunctionsContract`) and its discharge (`functionsContract_of`) are
stated once over an abstract preamble string and function list; each profile
supplies its own preamble, function list, render-identity fact and per-function
printability. Only the per-signature dispatched-body printability stays per
profile, since the dispatched bodies genuinely differ. -/
namespace Rumoca.FMI3.AdapterFunctionsPrinter
open CTree CTree.Printer CTree.Syntax
set_option autoImplicit false
variable {source : AST.Model}

private theorem named_type (name : String) (member : name ∈ RuntimePrinter.typedefs) :
    TypeSpelling RuntimePrinter.typedefs name := by
  have valid : RuntimePrinter.typedefs.all (CIdentifier.valid []) = true := by decide +kernel
  exact .named (.typedefName member (List.all_eq_true.mp valid name member))

/-- The reserved-record public factory function is printable: the shared admission
prefix followed by the reserved-record initializer (slot store, lifecycle
metadata, the counted state-region zero fill and the handle return). This is the
one dispatched factory body without an existing printability theorem, and it is
identical across profiles. -/
theorem factory_printable (model : Solve.FMI3Model source) (shape : Rumoca.Tensor.Shape) (kind : Kind)
    (tok : String) :
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

/-- Independent normal-context tokenization and per-function grammar for the
entire section following a profile's fixed declaration preamble. -/
def FunctionsContract (preamble : String) (fns : List Function) (adapter : String) : Prop :=
  ∃ text, adapter = preamble ++ text ∧
    FunctionsTokenization RuntimePrinter.typedefs text fns

/-- A profile's function section tokenizes maximally as its function list, given
its render identity (the render is the preamble followed by the concatenated
function renderings) and the per-function printability. -/
theorem functionsContract_of (preamble : String) (fns : List Function) (rendered : String)
    (renderEq : rendered = preamble ++ String.join (fns.map Function.render))
    (printable : ∀ fn ∈ fns, FunctionPrintable RuntimePrinter.typedefs fn) :
    FunctionsContract preamble fns rendered :=
  ⟨String.join (fns.map Function.render), renderEq, function_sequence_tokenization printable⟩

end Rumoca.FMI3.AdapterFunctionsPrinter
