import RumocaFMI3.ConstantFunctions

/-! Character-level identity for the constant adapter render, the constant analog
of `Rumoca.FMI3.adapter_chars` and `Rumoca.FMI3.TensorFunctions.tensor_adapter_chars`:
the checker certifies each emitted function separately, joins the character
chunks and binds them to the independently read complete file. -/
namespace Rumoca.FMI3.ConstantFunctions
open CTree
open Rumoca.Tensor (Shape)

theorem constant_adapter_chars {source : AST.Model} {n : Nat}
    (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List CTree.Signature) (before : List Char) (chunks : List (List Char)) (actual : List Char)
    (preamble : (functionPrefix m.name ++ "#include \"model.c\"\n" ++
      declarations m.shape (rates m)).toList = before)
    (matched : List.Forall₂ (fun fn chars => fn.render.toList = chars)
      (functions model m sigs) chunks)
    (bytes : before ++ chunks.flatten = actual) :
    render model m sigs = String.ofList actual :=
  RenderPlan.render_chars (constantPlan model m) sigs before chunks actual preamble matched bytes

end Rumoca.FMI3.ConstantFunctions
