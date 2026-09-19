import RumocaFMI3.Identifier
import RumocaC.StringLiteral
import Batteries.Data.List.Basic

/-! Profile-generic FMI 3 C-adapter render plan.

Every FMI 3 adapter profile (base scalar, tensor, constant) renders the same
five-piece C source: the model source-link prefix, the `model.c` include, a
per-profile declaration preamble, the concatenated helper renderings, and the
concatenated per-signature function renderings in header order. A `RenderPlan`
captures exactly the per-profile inputs of that shape (the model name, the
declaration preamble, the helper prefix and the per-signature body builder), and
the generic `RenderPlan.render` renders them. The render-identity facts, in
particular `RenderPlan.render_chars` (the checker certifies each emitted function
separately, joins the character chunks and binds them to the independently read
complete file), are proved once here for every profile rather than per profile. -/
namespace Rumoca.FMI3
open CTree
set_option autoImplicit false

/-- The per-profile inputs of the shared five-piece adapter render: the model
name that fixes the source-link prefix, the declaration preamble emitted after
the `model.c` include, the helper prefix, and the per-signature body builder. -/
structure RenderPlan where
  name : String
  preamble : String
  helpers : List CTree.Function
  body : CTree.Signature → CTree.Function

/-- The full emitted function list of a plan: the helper prefix followed by one
dispatched function per header signature, in header order. -/
def RenderPlan.functions (p : RenderPlan) (sigs : List CTree.Signature) : List CTree.Function :=
  p.helpers ++ sigs.map p.body

/-- The adapter render: the fixed source-link prefix and `model.c` include, the
declaration preamble, then the concatenated helper and dispatched-function
renderings, in header order. -/
def RenderPlan.render (p : RenderPlan) (sigs : List CTree.Signature) : String :=
  functionPrefix p.name ++ "#include \"model.c\"\n" ++ p.preamble ++
    String.join (p.helpers.map CTree.Function.render) ++
    String.join (sigs.map fun sig => (p.body sig).render)

/-- The render equals its fixed preamble followed by the concatenated rendering
of the full function list. -/
theorem RenderPlan.rendered_functions (p : RenderPlan) (sigs : List CTree.Signature) :
    p.render sigs = functionPrefix p.name ++ "#include \"model.c\"\n" ++ p.preamble ++
      String.join ((p.functions sigs).map CTree.Function.render) := by
  apply String.toList_injective
  simp [RenderPlan.render, RenderPlan.functions, String.toList_append, CString.join_toList,
    List.flatMap_map, List.append_assoc]

/-- Each header signature is rendered exactly once at its actual list slot. -/
theorem RenderPlan.rendered_member (p : RenderPlan) (sigs : List CTree.Signature)
    (sig : CTree.Signature) (member : sig ∈ sigs) :
    ∃ before after : String, p.render sigs = before ++ (p.body sig).render ++ after := by
  obtain ⟨left, right, rfl⟩ := List.mem_iff_append.mp member
  refine ⟨functionPrefix p.name ++ "#include \"model.c\"\n" ++ p.preamble ++
    String.join (p.helpers.map CTree.Function.render) ++
    String.join (left.map fun sig => (p.body sig).render),
    String.join (right.map fun sig => (p.body sig).render), ?_⟩
  apply String.toList_injective
  simp [RenderPlan.render, String.toList_append, CString.join_toList,
    List.flatMap_map, List.append_assoc]

/-- Every helper is a concrete fragment of the same emitted function list. -/
theorem RenderPlan.rendered_helper (p : RenderPlan) (sigs : List CTree.Signature)
    (fn : CTree.Function) (member : fn ∈ p.helpers) :
    ∃ before after : String, p.render sigs = before ++ fn.render ++ after := by
  obtain ⟨left, right, same⟩ := List.mem_iff_append.mp member
  refine ⟨functionPrefix p.name ++ "#include \"model.c\"\n" ++ p.preamble ++
    String.join (left.map CTree.Function.render),
    String.join (right.map CTree.Function.render) ++
      String.join (sigs.map fun sig => (p.body sig).render), ?_⟩
  apply String.toList_injective
  simp [RenderPlan.render, same, String.toList_append, CString.join_toList,
    List.flatMap_map, List.append_assoc]

private theorem RenderPlan.function_chunks (fns : List CTree.Function) (chunks : List (List Char))
    (matched : List.Forall₂ (fun fn chars => fn.render.toList = chars) fns chunks) :
    fns.flatMap (fun fn => fn.render.toList) = chunks.flatten := by
  induction matched with
  | nil => rfl
  | cons head tail ih => simp only [List.flatMap_cons, List.flatten_cons, head, ih]

/-- The checker can certify each emitted function separately, then join the
character chunks and bind them to the independently read complete file. This is
the single render-identity lemma every profile's adapter-bytes certificate
instantiates. -/
theorem RenderPlan.render_chars (p : RenderPlan) (sigs : List CTree.Signature)
    (before : List Char) (chunks : List (List Char)) (actual : List Char)
    (preamble : (functionPrefix p.name ++ "#include \"model.c\"\n" ++ p.preamble).toList = before)
    (matched : List.Forall₂ (fun fn chars => fn.render.toList = chars) (p.functions sigs) chunks)
    (bytes : before ++ chunks.flatten = actual) :
    p.render sigs = String.ofList actual := by
  apply String.toList_injective
  rw [RenderPlan.rendered_functions]
  rw [String.toList_append, preamble, CString.join_toList, List.flatMap_map,
    RenderPlan.function_chunks _ _ matched, String.toList_ofList]
  exact bytes

end Rumoca.FMI3
