import RumocaC.NullComparison
import RumocaC.ExpressionPrinter

/-! The same typed null constant has the independent shared printer derivation
and the C null-pointer value. This binds the reusable expression's actual
characters; complete functions still require their usual artifact contracts. -/
namespace Rumoca.CNull
open CTree CTree.Syntax CTree.Printer CMemory CBody

theorem literal_printable (typedefs : List String) : Printable typedefs Expr.nullPointer :=
  .cast (.pointer (text := "void") (.named (.primitive (by decide +kernel)))) .natural

theorem literal_renders (typedefs : List String) : Renders typedefs Expr.nullPointer :=
  expression_renders (literal_printable typedefs)

variable [interface : CInterface]

theorem literal_contract (typedefs : List String)
    (type : interface.types "void *" = some .pointer) :
    Renders typedefs Expr.nullPointer ∧
      ∀ env heap, eval env heap Expr.nullPointer = some (.pointer none) :=
  ⟨literal_renders typedefs, literal_eval type⟩

end Rumoca.CNull
