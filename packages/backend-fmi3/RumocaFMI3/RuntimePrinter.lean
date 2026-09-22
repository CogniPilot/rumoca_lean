import RumocaC.TreeTokenization
import RumocaC.NullPointerPrinter
import RumocaC.Initialization
import RumocaFMI3.Runtime
import RumocaFMI3.IdentityPrinter
import RumocaFMI3.StaticFactoryPrinter
import RumocaC.AtomicScanPrinter

/-! Instantiate the shared C printer contract for every existing FMI runtime
body and helper. Typedef spellings are explicit surrounding-context premises;
their actual declarations, type constraints and public-call behavior require
separate contracts. No function-specific token skeleton is used. -/
namespace Rumoca.FMI3.RuntimePrinter
open CTree CTree.Printer CTree.Syntax

private theorem instance_type : TypeSpelling typedefs "Instance *" :=
  TypeSpelling.pointer (text := "Instance")
    (TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)))

private theorem instance_value_type : TypeSpelling typedefs "Instance" :=
  TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel))

private theorem handle_type : TypeSpelling typedefs "fmi3Instance" :=
  TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel))

private theorem size_type : TypeSpelling typedefs "size_t" :=
  TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel))

private theorem count_type : TypeSpelling typedefs "uint64_t" :=
  TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel))

private theorem double_type : TypeSpelling typedefs "double" :=
  TypeSpelling.named (.primitive (by decide +kernel))

private theorem int_type : TypeSpelling typedefs "int" :=
  TypeSpelling.named (.primitive (by decide +kernel))

private theorem status_type : TypeSpelling typedefs "fmi3Status" :=
  TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel))

private theorem boolean_type : TypeSpelling typedefs "fmi3Boolean" :=
  TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel))

private theorem model_pointer_type : TypeSpelling typedefs "Model *" :=
  TypeSpelling.pointer (text := "Model")
    (TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)))

private theorem const_model_pointer_type : TypeSpelling typedefs "const Model *" :=
  TypeSpelling.const model_pointer_type

private theorem const_char_pointer_type : TypeSpelling typedefs "const char *" :=
  TypeSpelling.const (TypeSpelling.pointer (text := "char")
    (TypeSpelling.named (.primitive (by decide +kernel))))

private theorem void_type : TypeSpelling typedefs "void" :=
  TypeSpelling.named (.primitive (by decide +kernel))

private theorem any_printable (each : ∀ e ∈ es, Printable typedefs e) :
    Printable typedefs (Runtime.any es) := by
  induction es with
  | nil => exact .natural
  | cons e es ih =>
      exact .binary (each e (by simp)) (ih (fun e member => each e (by simp [member])))

private theorem allowed_printable (command : Command) :
    Printable typedefs (Runtime.allowedExpression command) := by
  unfold Runtime.allowedExpression Runtime.either Runtime.both Runtime.eqv Runtime.field
  apply Printable.binary <;> apply Printable.binary
  all_goals first
    | apply Printable.binary
      · exact .field (.identifier (by decide +kernel)) trivial trivial (by decide +kernel)
      · exact .natural
    | apply any_printable
      intro expr member
      obtain ⟨mode, member, rfl⟩ := List.mem_map.mp member
      apply Printable.binary
      · exact .field (.identifier (by decide +kernel)) trivial trivial (by decide +kernel)
      · exact .natural

private theorem require_printable (command : Command) :
    ∀ stmt ∈ Runtime.require command, ItemPrintable typedefs stmt := by
  simp only [Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.reject,
    Runtime.branch, Runtime.negate, Runtime.fail, Runtime.ret, Runtime.call,
    Runtime.v, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    or_imp, forall_and, forall_eq]
  repeat first
    | exact CNull.literal_printable _
    | exact instance_type
    | exact allowed_printable command
    | apply And.intro
    | apply ItemPrintable.declare
    | apply ItemPrintable.branch
    | apply ItemPrintable.returnValue
    | apply Printable.cast
    | apply Printable.binary
    | apply Printable.not
    | apply Printable.call
    | exact Printable.string
    | apply Printable.identifier
    | solve | intro stmt impossible; cases impossible
    | decide +kernel
    | simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Postfix]

private theorem mode_guard_printable (command : Command) :
    ItemPrintable typedefs (Runtime.modeGuard command) :=
  require_printable command _ (by simp [Runtime.require])

set_option maxHeartbeats 4000000 in
theorem body_printable (model : Solve.FMI3Model source) (signature : Signature) :
    ∀ stmt ∈ Runtime.body model signature, ItemPrintable typedefs stmt := by
  unfold Runtime.body
  split <;> (try split)
  all_goals first
    | exact (StaticFactory.Printer.factory_printable model .me).2
    | exact (StaticFactory.Printer.factory_printable model .cs).2
    | exact StaticFactory.Printer.release_printable.2
    | skip
  all_goals
    simp only [DebugLogging.code, DebugLogging.missing, DebugLogging.failure,
      DebugLogging.validation, DebugLogging.iteration, DebugLogging.rejectNull,
      DebugLogging.comparison, DebugLogging.rejectDifference, DebugLogging.category,
      DebugLogging.finish, DebugLogging.writeLogging, CLoops.loop, CLoops.counterStep,
      Runtime.instancePrefix, Runtime.countLoop,
      Runtime.getFloat64, Runtime.setFloat64, Runtime.setFloat64Values,
      Runtime.scalarAccessCheck, Runtime.pointerCheck,
      Runtime.doStep, Runtime.stepRounding, Runtime.stepClock, Runtime.stepGrid,
      Runtime.stepSolve, Runtime.stepDiscard, Runtime.initialTime, Runtime.eventTime, Runtime.completedTime,
      Runtime.invalidTime, CInitialization.Emission.statement, CInitialization.value_zero,
      Runtime.raiseField, Runtime.reject, Runtime.branch, Runtime.fail, Runtime.ret,
      Runtime.put, Runtime.out, Runtime.ok, Runtime.setMode, Runtime.log,
      Runtime.v, Runtime.n, Runtime.call, Runtime.field, Runtime.x,
      Runtime.eqv, Runtime.nev, Runtime.lt, Runtime.gt, Runtime.le,
      Runtime.both, Runtime.either, Runtime.negate, Runtime.finite, Runtime.mode,
      Runtime.any, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and,
      List.cons_append, List.nil_append, forall_eq]
    repeat first
      | exact CNull.literal_printable _
      | exact require_printable _
      | exact mode_guard_printable _
      | exact instance_type
      | exact instance_value_type
      | exact handle_type
      | exact size_type
      | exact count_type
      | exact double_type
      | exact int_type
      | exact boolean_type
      | apply And.intro
      | apply ItemPrintable.declare
      | apply ItemPrintable.assign
      | apply ItemPrintable.branch
      | apply ItemPrintable.whileLoop
      | apply ItemPrintable.eval
      | apply ItemPrintable.returnValue
      | apply Printable.cast
      | apply Printable.sizeof
      | apply Printable.binary
      | apply Printable.not
      | apply Printable.dereference
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

theorem function_printable (model : Solve.FMI3Model source) (signature : Signature)
    (valid : SignaturePrintable typedefs signature) :
    FunctionPrintable typedefs (Runtime.function model signature) :=
  ⟨valid, body_printable model signature⟩

theorem function_tokenization (model : Solve.FMI3Model source) (signature : Signature)
    (valid : SignaturePrintable typedefs signature) :
    FunctionTokenization typedefs (Runtime.function model signature).render
      (Runtime.function model signature) :=
  (CTree.Printer.function_denotes (function_printable model signature valid)).tokenization

private theorem reserve_printable : FunctionPrintable typedefs CAtomicScan.function :=
  CAtomicScan.Printer.function_printable_in typedefs size_type
    (TypeSpelling.pointer (text := "volatile atomic_bool")
      (TypeSpelling.volatile (text := "atomic_bool")
        (.named (.typedefName (by decide +kernel) (by decide +kernel))))) (by
      intro name member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

theorem helpers_printable : ∀ fn ∈ Runtime.helpers, FunctionPrintable typedefs fn := by
  intro fn member
  simp only [Runtime.helpers, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact Identity.Printer.function_printable_in typedefs (by decide) (by decide) (by decide)
    | exact reserve_printable
    | skip
  all_goals simp only [FunctionPrintable, SignaturePrintable, ParameterPrintable,
    Runtime.setMode, Runtime.put, Runtime.mode, Runtime.log, Runtime.branch,
    Runtime.both, Runtime.nev, Runtime.field, Runtime.v, Runtime.n, Runtime.ret, Runtime.call,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  all_goals repeat first
    | exact instance_type
    | exact status_type
    | exact model_pointer_type
    | exact const_model_pointer_type
    | exact const_char_pointer_type
    | exact count_type
    | exact double_type
    | exact void_type
    | exact CNull.literal_printable _
    | apply And.intro
    | apply ItemPrintable.assign
    | apply ItemPrintable.declare
    | apply ItemPrintable.whileLoop
    | apply ItemPrintable.branch
    | apply ItemPrintable.eval
    | apply ItemPrintable.returnValue
    | apply Printable.binary
    | apply Printable.cast
    | apply Printable.not
    | apply Printable.address
    | apply Printable.index
    | apply Printable.call
    | apply Printable.field
    | exact Printable.natural
    | exact Printable.string
    | apply Printable.identifier
    | solve | intro stmt impossible; cases impossible
    | decide +kernel
    | simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        Postfix, FieldBase]

end Rumoca.FMI3.RuntimePrinter
