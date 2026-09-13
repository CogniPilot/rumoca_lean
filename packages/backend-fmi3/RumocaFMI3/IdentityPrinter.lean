import RumocaFMI3.IdentityCode
import RumocaC.FunctionPrinter
import RumocaC.TreeTokenization

/-! Independent lexical/tree certificate for the exact private validator.
The FMI typedef, string-library headers and surrounding translation unit need
their separate binding contracts. -/
namespace Rumoca.FMI3.Identity.Printer
open CTree CTree.Printer CTree.Syntax

def typedefs : List String := ["size_t", "fmi3Boolean"]

/-- Every ordinary identifier must remain distinct from the enclosing typedefs. -/
def identifiers : List String :=
  ["rumoca_valid_identity", "name", "token", "expected", "whitespace",
    "length", "prefix", "difference", "strlen", "strspn", "strcmp"]

private theorem identifier_valid (names : List String)
    (valid : identifiers.all (CIdentifier.valid names) = true)
    (name : String) (member : name ∈ identifiers) : CIdentifier.valid names name = true :=
  List.all_eq_true.mp valid name member

private theorem size_type (names : List String) (member : "size_t" ∈ names) : TypeSpelling names "size_t" :=
  .named (.typedefName member (by decide))
private theorem boolean_type (names : List String) (member : "fmi3Boolean" ∈ names) : TypeSpelling names "fmi3Boolean" :=
  .named (.typedefName member (by decide))
private theorem integer_type (names : List String) : TypeSpelling names "int" := .named (.primitive (by decide))
private theorem char_pointer (names : List String) : TypeSpelling names "const char *" :=
  TypeSpelling.pointer (text := "const char")
    (TypeSpelling.const (text := "char") (.named (.primitive (by decide))))
private theorem void_pointer (names : List String) : TypeSpelling names "void *" :=
  TypeSpelling.pointer (text := "void") (.named (.primitive (by decide)))

theorem function_printable_in (names : List String) (size : "size_t" ∈ names)
    (boolean : "fmi3Boolean" ∈ names)
    (valid : identifiers.all (CIdentifier.valid names) = true) :
    FunctionPrintable names function := by
  constructor
  · refine ⟨boolean_type names boolean, identifier_valid names valid _ (by decide), ?_⟩
    intro parameter member
    simp only [function, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      exact ⟨char_pointer names, identifier_valid names valid _ (by decide)⟩
  · simp only [function, nullCheck, falseReturn, measure, measurePrefix, blank,
      compareToken, comparisonReturn, Expr.nullPointer, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    repeat first
      | exact size_type names size
      | exact boolean_type names boolean
      | exact integer_type names
      | exact void_pointer names
      | exact identifier_valid names valid _ (by decide)
      | apply And.intro
      | apply ItemPrintable.declare
      | apply ItemPrintable.assign
      | apply ItemPrintable.branch
      | apply ItemPrintable.returnValue
      | apply Printable.cast
      | apply Printable.binary
      | apply Printable.call
      | exact Printable.natural
      | apply Printable.identifier
      | solve | intro stmt impossible; cases impossible
      | decide +kernel
      | simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Postfix]

theorem function_printable : FunctionPrintable typedefs function :=
  function_printable_in typedefs (by decide) (by decide) (by decide)

theorem function_denotes : FunctionDenotes typedefs function.render function :=
  CTree.Printer.function_denotes function_printable

theorem function_tokenization : FunctionTokenization typedefs function.render function :=
  function_denotes.tokenization

end Rumoca.FMI3.Identity.Printer
