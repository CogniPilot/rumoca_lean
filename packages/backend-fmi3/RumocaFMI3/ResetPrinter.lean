import RumocaC.FunctionPrinter
import RumocaC.NullPointerPrinter
import RumocaFMI3.ResetCalls

/-! Instantiate the shared function-printer theorem on the actual reset CTree.
The context records the type names required from the surrounding adapter and
FMI headers; their declaration, scope and ABI meanings remain separate. No
reset-specific token skeleton or executable C parser is used in this proof. -/
namespace Rumoca.FMI3.Reset.Printer
open CTree CTree.Printer CTree.Syntax

def typedefs : List String := ["Instance", "fmi3Status", "fmi3Instance"]

private theorem instance_type : TypeSpelling typedefs "Instance *" :=
  TypeSpelling.pointer (text := "Instance")
    (TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)))

private theorem status_type : TypeSpelling typedefs "fmi3Status" :=
  TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel))

private theorem handle_type : TypeSpelling typedefs "fmi3Instance" :=
  TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel))

private theorem double_type : TypeSpelling typedefs "double" :=
  TypeSpelling.named (.primitive (by decide +kernel))

set_option maxHeartbeats 1000000 in
theorem function_printable (m : Solve.FMI3Model source) :
    FunctionPrintable typedefs (Runtime.function m signature) := by
  constructor
  · refine ⟨status_type, ?_, ?_⟩
    · change CIdentifier.valid typedefs "fmi3Reset" = true
      decide +kernel
    · intro param member
      have same : param = ⟨"fmi3Instance", "instance", false⟩ := by
        simpa only [Runtime.function, signature, List.mem_singleton] using member
      subst param
      exact ⟨handle_type, by decide +kernel⟩
  · simp only [Runtime.function, Runtime.body, signature,
      Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.reject,
      Runtime.branch, Runtime.negate, Runtime.allowedExpression, Runtime.either,
      Runtime.both, Runtime.eqv, Runtime.any, Runtime.field, Runtime.mode,
      permittedModes, Mode.code, Runtime.fail, Runtime.call, Runtime.ret,
      Runtime.v, Runtime.n, Runtime.x, Runtime.put, Runtime.setMode, Runtime.ok,
      CInitialization.Emission.statement, CInitialization.value_zero,
      List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    repeat first
      | exact CNull.literal_printable _
      | exact instance_type
      | exact double_type
      | apply And.intro
      | apply ItemPrintable.declare
      | apply ItemPrintable.assign
      | apply ItemPrintable.branch
      | apply ItemPrintable.returnValue
      | apply Printable.cast
      | apply Printable.binary
      | apply Printable.not
      | apply Printable.call
      | apply Printable.field
      | exact Printable.natural
      | exact Printable.string
      | apply Printable.identifier
      | solve | intro stmt impossible; cases impossible
      | decide +kernel
      | simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
          Postfix, FieldBase]

theorem function_renders (m : Solve.FMI3Model source) :
    FunctionRenders typedefs (Runtime.function m signature) :=
  CTree.Printer.function_renders (function_printable m)

theorem render_denotes (m : Solve.FMI3Model source) :
    FunctionDenotes typedefs (Runtime.function m signature).render (Runtime.function m signature) :=
  CTree.Printer.function_denotes (function_printable m)

end Rumoca.FMI3.Reset.Printer
