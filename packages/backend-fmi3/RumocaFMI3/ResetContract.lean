import RumocaFMI3.ResetSyntax
import RumocaFMI3.LiteralRejection

/-! Reset's function-text and execution contract over the actual rendered
definition list. This is a fragment contract; it does not establish that a
native preprocessor/linker gives an arbitrary containing file these meanings.
Allocated typed storage and the explicit FMI C interface remain premises. -/
noncomputable section
namespace Rumoca.FMI3.Reset
open CTree CMemory
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

structure FunctionContract (m : Solve.FMI3Model source) (text : String) : Prop where
  printed : text = (Runtime.function m signature).render
  denoted : Syntax.Denotes text
  successful : ∀ (sigs : List Signature), signature ∈ sigs →
    ((LiteralPreparation.functions m sigs).map (fun fn => fn.signature.name)).Nodup →
    ∀ (heap : Heap) (p : Address) (kind : Kind) (mode : Mode), Storage heap p →
    load heap (p.member "kind") = some (.integer kind.code) →
    load heap (p.member "mode") = some (.integer mode.code) →
    ∀ behavior, (CCalls.Typed.machine (LiteralPreparation.program m sigs)).Behaves
      (.calling "fmi3Reset" [.pointer (some p)] heap .done) behavior ↔
      behavior = .terminates ⟨.integer 0, finalHeap heap p⟩
  null : ∀ (sigs : List Signature), signature ∈ sigs →
    ((LiteralPreparation.functions m sigs).map (fun fn => fn.signature.name)).Nodup → ∀ heap behavior,
    (CCalls.Typed.machine (LiteralPreparation.program m sigs)).Behaves
      (.calling "fmi3Reset" [.pointer none] heap .done) behavior ↔
      behavior = .terminates ⟨.integer 3, heap⟩

theorem rendered_contract (m : Solve.FMI3Model source) :
    FunctionContract m (Runtime.function m signature).render := by
  refine ⟨rfl, Syntax.render_denotes m, ?_, ?_⟩
  · intro sigs member unique heap p kind mode storage hk hm behavior
    exact call_behaviors m (LiteralPreparation.program m sigs) heap p kind mode
      (LiteralRejection.function_bound m sigs unique signature member)
      storage hk hm behavior
  · intro sigs member unique heap behavior
    exact null_behaviors m (LiteralPreparation.program m sigs) heap
      (LiteralRejection.function_bound m sigs unique signature member) behavior

omit static in
/-- The full renderer places the certified fragment at a function-list slot.
This decomposition alone is not a translation-unit or preprocessing theorem. -/
theorem rendered_member (m : Solve.FMI3Model source) (sigs : List Signature)
    (member : signature ∈ sigs) :
    ∃ before after : String,
      Runtime.render m sigs = before ++ (Runtime.function m signature).render ++ after := by
  obtain ⟨left, right, rfl⟩ := List.mem_iff_append.mp member
  refine ⟨functionPrefix m.name ++ "#include \"model.c\"\n" ++ Runtime.declarations ++
      String.join (Runtime.helpers.map Function.render) ++
      String.join (left.map fun sig => (Runtime.function m sig).render),
    String.join (right.map fun sig => (Runtime.function m sig).render), ?_⟩
  apply String.toList_injective
  simp [Runtime.render, String.toList_append, CString.join_toList,
    List.flatMap_map, List.append_assoc]

end Rumoca.FMI3.Reset
