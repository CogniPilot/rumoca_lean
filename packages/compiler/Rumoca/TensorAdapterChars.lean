import RumocaFMI3.TensorFunctions

/-! Character-level identity for the tensor adapter render, the tensor analog of
`Rumoca.FMI3.adapter_chars`: the checker certifies each emitted function
separately, joins the character chunks and binds them to the independently read
complete file. -/
namespace Rumoca.FMI3.TensorFunctions
open CTree
open Rumoca.Tensor (Shape)

theorem tensor_adapter_chars {source : AST.Model} {shape : Shape}
    (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List CTree.Signature) (before : List Char) (chunks : List (List Char)) (actual : List Char)
    (preamble : (functionPrefix m.name ++ "#include \"model.c\"\n" ++
      TensorStorage.declarations shape m.hasOutput).toList = before)
    (matched : List.Forall₂ (fun fn chars => fn.render.toList = chars)
      (functions model m sigs) chunks)
    (bytes : before ++ chunks.flatten = actual) :
    render model m sigs = String.ofList actual :=
  RenderPlan.render_chars (tensorPlan model m) sigs before chunks actual preamble matched bytes

end Rumoca.FMI3.TensorFunctions
