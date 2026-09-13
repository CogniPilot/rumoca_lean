import RumocaC.AtomicScanCode
import RumocaC.FunctionPrinter
import RumocaC.TreeTokenization

/-! The existing certified printer applied to the actual reservation helper.
Surrounding typedef definitions, <stdatomic.h> macros, object declarations and
native linkage are separate from this ordinary-function lexical contract. -/
namespace Rumoca.CAtomicScan.Printer
open CTree CTree.Printer CTree.Syntax

def typedefs : List String := ["size_t", "atomic_bool"]

private theorem size_type : TypeSpelling typedefs "size_t" :=
  .named (.typedefName (by decide +kernel) (by decide +kernel))

private theorem boolean_type : TypeSpelling typedefs "_Bool" :=
  .named (.primitive (by decide +kernel))

private theorem flag_pointer : TypeSpelling typedefs "volatile atomic_bool *" :=
  TypeSpelling.pointer (text := "volatile atomic_bool")
    (TypeSpelling.volatile (text := "atomic_bool")
      (.named (.typedefName (by decide +kernel) (by decide +kernel))))

theorem function_printable : FunctionPrintable typedefs function := by
  constructor
  · refine ⟨size_type, by decide +kernel, ?_⟩
    intro parameter member
    simp only [function, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨flag_pointer, by decide +kernel⟩
    · exact ⟨size_type, by decide +kernel⟩
  · simp only [function, scan, attempt, selected, advance, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    repeat first
      | exact size_type
      | exact boolean_type
      | exact TypeSpelling.const size_type
      | apply And.intro
      | apply ItemPrintable.declare
      | apply ItemPrintable.assign
      | apply ItemPrintable.branch
      | apply ItemPrintable.whileLoop
      | apply ItemPrintable.returnValue
      | apply Printable.cast
      | apply Printable.binary
      | apply Printable.not
      | apply Printable.call
      | apply Printable.address
      | apply Printable.index
      | exact Printable.natural
      | apply Printable.identifier
      | solve | intro stmt impossible; cases impossible
      | decide +kernel
      | simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
          Postfix]

theorem function_denotes : FunctionDenotes typedefs function.render function :=
  CTree.Printer.function_denotes function_printable

theorem function_tokenization : FunctionTokenization typedefs function.render function :=
  function_denotes.tokenization

end Rumoca.CAtomicScan.Printer
