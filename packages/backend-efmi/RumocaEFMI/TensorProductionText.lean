import RumocaEFMI.TensorProductionProofs
import RumocaC.StringLiteral

/-! Bind the tensor Production Code translation unit to an independently read
byte sequence, one certified fragment at a time. Like the FMI 3 tensor kernel
text (`Rumoca.TensorKernel.chars`), the Production Code render is the join of the
certified kernel-entry renders, the interface header and the method-function
renders; this file exposes that fragment list and the character-chunk binding so
the actual-file checker certifies each fragment separately and joins the chunks. -/
namespace Rumoca.EFMI.TensorProduction
open Rumoca.CTree

/-- The Production Code translation unit fragments in emission order: the certified
kernel pieces, the interface header, and the three method-function renders. -/
def renderPieces : List String := kernelPieces ++ header :: functions.map Function.render

theorem render_toList : render.toList = renderPieces.flatMap String.toList := by
  simp only [render, kernelText, renderPieces, String.toList_append, CString.join_toList,
    List.flatMap_append, List.flatMap_cons, List.append_assoc]

private theorem piece_chunks (ps : List String) (chunks : List (List Char))
    (matched : List.Forall₂ (fun s cs => s.toList = cs) ps chunks) :
    ps.flatMap String.toList = chunks.flatten := by
  induction matched with
  | nil => rfl
  | cons head tail ih => simp only [List.flatMap_cons, List.flatten_cons, head, ih]

/-- The checker certifies each fragment separately, joins the character chunks and
binds them to the independently read Production Code file. -/
theorem render_chars (chunks : List (List Char)) (actual : List Char)
    (matched : List.Forall₂ (fun s cs => s.toList = cs) renderPieces chunks)
    (bytes : chunks.flatten = actual) : render = String.ofList actual := by
  apply String.toList_injective
  rw [render_toList, piece_chunks _ _ matched, bytes, String.toList_ofList]

end Rumoca.EFMI.TensorProduction
