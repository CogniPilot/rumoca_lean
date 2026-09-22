import RumocaFMI3.StaticFactoryCode
import RumocaFMI3.StaticReleaseCode
import RumocaFMI3.PrinterTypes
import RumocaC.FunctionPrinter
import RumocaC.TreeTokenization
import RumocaC.NullPointerPrinter
import RumocaC.Initialization

/-! The existing certified C printer applied to both full static factories
and release. These are ordinary-function grammar/token contracts. Their
surrounding declarations, typedef meanings and atomic macros remain separate
translation-unit obligations. The runtime uses these factory/release bodies;
these printer theorems alone do not discharge those surrounding obligations. -/
namespace Rumoca.FMI3.StaticFactory.Printer
open CTree CTree.Printer CTree.Syntax

private theorem named_type (name : String) (member : name ∈ RuntimePrinter.typedefs) :
    TypeSpelling RuntimePrinter.typedefs name := by
  have valid : RuntimePrinter.typedefs.all (CIdentifier.valid []) = true := by decide +kernel
  exact .named (.typedefName member (List.all_eq_true.mp valid name member))

private theorem instance_pointer : TypeSpelling RuntimePrinter.typedefs "Instance *" :=
  TypeSpelling.pointer (text := "Instance") (named_type _ (by decide +kernel))

theorem signature_printable (kind : Kind) :
    SignaturePrintable RuntimePrinter.typedefs (FactoryArguments.signature kind) := by
  cases kind <;>
    simp only [SignaturePrintable, ParameterPrintable, FactoryArguments.signature, Identity.factoryName,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
  all_goals
    repeat first
      | apply And.intro
      | exact named_type _ (by decide +kernel)
      | exact TypeSpelling.const (named_type "fmi3ValueReference" (by decide +kernel))
      | decide +kernel

theorem factory_printable (model : Solve.FMI3Model source) (kind : Kind) :
    FunctionPrintable RuntimePrinter.typedefs (function model kind) := by
  refine ⟨signature_printable kind, ?_⟩
  cases kind <;>
    simp only [function, FactoryPrefix.body, FactoryPrefix.entry, FactoryPrefix.validation,
      FactoryPrefix.identityGuard, FactoryPrefix.capabilityGuard, FactoryRejection.code, FactoryRejection.logCall,
      code, reserve, guard, exhausted, initializeInstance, selectInstance, CAtomicScan.function, Identity.function,
      InstanceSlot.code, InstanceSlot.statement, InstanceInitialization.code, InstanceInitialization.put,
      InstanceInitialization.returnHandle, InstanceInitialization.state, InstanceInitialization.field,
      CInitialization.Emission.statement, CInitialization.value_zero,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      or_imp, forall_and, forall_eq]
  all_goals
    repeat first
      | exact instance_pointer
      | exact named_type _ (by decide +kernel)
      | exact (TypeSpelling.named (.primitive (by decide +kernel)) : TypeSpelling RuntimePrinter.typedefs "double")
      | apply And.intro
      | apply ItemPrintable.declare
      | apply ItemPrintable.assign
      | apply ItemPrintable.branch
      | apply ItemPrintable.eval
      | apply ItemPrintable.returnValue
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
      | simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Postfix, FieldBase]

theorem release_printable : FunctionPrintable RuntimePrinter.typedefs StaticRelease.function := by
  constructor
  · refine ⟨.named (.primitive (by decide +kernel)), by decide +kernel, ?_⟩
    intro param member
    simp only [StaticRelease.function, List.mem_cons, List.not_mem_nil, or_false] at member
    subst param
    exact ⟨named_type _ (by decide +kernel), by decide +kernel⟩
  · simp only [StaticRelease.function, StaticRelease.guard, StaticRelease.clear, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    repeat first
      | exact CNull.literal_printable _
      | exact instance_pointer
      | exact (TypeSpelling.named (.primitive (by decide +kernel)) : TypeSpelling RuntimePrinter.typedefs "_Bool")
      | apply And.intro
      | apply ItemPrintable.declare
      | apply ItemPrintable.branch
      | apply ItemPrintable.eval
      | exact ItemPrintable.returnVoid
      | apply Printable.cast
      | apply Printable.binary
      | apply Printable.address
      | apply Printable.call
      | apply Printable.field
      | apply Printable.index
      | exact Printable.natural
      | apply Printable.identifier
      | solve | intro stmt impossible; cases impossible
      | decide +kernel
      | simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Postfix, FieldBase]

theorem factory_denotes (model : Solve.FMI3Model source) (kind : Kind) :
    FunctionDenotes RuntimePrinter.typedefs (function model kind).render (function model kind) :=
  CTree.Printer.function_denotes (factory_printable model kind)

theorem factory_tokenization (model : Solve.FMI3Model source) (kind : Kind) :
    FunctionTokenization RuntimePrinter.typedefs (function model kind).render (function model kind) :=
  (factory_denotes model kind).tokenization

theorem release_denotes :
    FunctionDenotes RuntimePrinter.typedefs StaticRelease.function.render StaticRelease.function :=
  CTree.Printer.function_denotes release_printable

theorem release_tokenization :
    FunctionTokenization RuntimePrinter.typedefs StaticRelease.function.render StaticRelease.function :=
  release_denotes.tokenization

end Rumoca.FMI3.StaticFactory.Printer
