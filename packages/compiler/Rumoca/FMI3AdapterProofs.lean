import Rumoca.FMI3ResetProofs
import Rumoca.FMI3NameProofs
import RumocaFMI3.AdapterPreprocessing

/-! Complete adapter byte identity, together with the current independently
denoted reset function and its source consequence. Other function execution,
whole-C syntax/preprocessing, official-header meanings and native ABI remain
separate obligations. Exact renderer identity is not their substitute. -/
namespace Rumoca.FMI3

private theorem function_chunks (functions : List CTree.Function) (chunks : List (List Char))
    (matched : List.Forall₂ (fun fn chars => fn.render.toList = chars) functions chunks) :
    functions.flatMap (fun fn => fn.render.toList) = chunks.flatten := by
  induction matched with
  | nil => rfl
  | cons head tail ih => simp only [List.flatMap_cons, List.flatten_cons, head, ih]

/-- The checker can certify each function separately, then join character
chunks and bind them to the independently read complete file. -/
theorem adapter_chars (m : Solve.FMI3Model source) (sigs : List CTree.Signature)
    (before : List Char) (chunks : List (List Char)) (actual : List Char)
    (preamble : (functionPrefix m.name ++ "#include \"model.c\"\n" ++
      Runtime.declarations).toList = before)
    (matched : List.Forall₂ (fun fn chars => fn.render.toList = chars)
      (LiteralPreparation.functions m sigs) chunks)
    (bytes : before ++ chunks.flatten = actual) :
    Runtime.render m sigs = String.ofList actual := by
  apply String.toList_injective
  rw [LiteralPreparation.rendered_functions]
  rw [String.toList_append, preamble, CString.join_toList, List.flatMap_map,
    function_chunks _ _ matched, String.toList_ofList]
  exact bytes

def AdapterContract (a : Artifact input) (adapter : String) : Prop :=
  ∃ sigs : List CTree.Signature,
    ((LiteralPreparation.functions a.solve.prepareFMI3 sigs).map
      (fun fn => fn.signature.name)).Nodup ∧
    Reset.signature ∈ sigs ∧
    Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
    CTree.Preprocessing.Stable adapter.toList ∧
    ∀ static : StaticLiterals,
      @Reset.FunctionContract static a.parsed.ast a.solve.prepareFMI3
        (Runtime.function a.solve.prepareFMI3 Reset.signature).render

theorem adapter_correct (a : Artifact input) (sigs : List CTree.Signature)
    (unique : ((LiteralPreparation.functions a.solve.prepareFMI3 sigs).map
      (fun fn => fn.signature.name)).Nodup)
    (member : Reset.signature ∈ sigs)
    (spellings : ∀ sig ∈ sigs, CTree.Preprocessing.SignatureInputs sig)
    (printed : Runtime.render a.solve.prepareFMI3 sigs = adapter) : AdapterContract a adapter :=
  ⟨sigs, unique, member, printed,
    printed ▸ AdapterPreprocessing.render_stable a.solve.prepareFMI3 sigs
      (AdapterPreprocessing.name_plain (parsed_name a.parsed)) spellings,
    fun _ => Reset.rendered_contract _⟩

/-- Extract character-rewrite stability from the contract on the actual file.
Macro expansion and included-header interpretation remain separate. -/
theorem adapter_preprocessed (contract : AdapterContract a adapter)
    (steps : Relation.ReflTransGen CString.Rewrite adapter.toList out) : out = adapter.toList := by
  obtain ⟨_, _, _, _, characters, _⟩ := contract
  exact characters.preprocessed steps

/-- The actual adapter contains reset text with the shared C function grammar.
This keeps its position in the independently read file and the tree used by the
execution contract together. Whole-file preprocessing and header interpretation
are still separate obligations. -/
theorem adapter_reset_syntax (contract : AdapterContract a adapter) :
    ∃ before text after : String,
      adapter = before ++ text ++ after ∧
      CTree.Printer.FunctionDenotes Reset.Printer.typedefs text
        (Runtime.function a.solve.prepareFMI3 Reset.signature) := by
  obtain ⟨sigs, unique, member, printed, stable, reset⟩ := contract
  obtain ⟨before, after, located⟩ := Reset.rendered_member a.solve.prepareFMI3 sigs member
  refine ⟨before, (Runtime.function a.solve.prepareFMI3 Reset.signature).render, after,
    printed ▸ located, ?_⟩
  exact Reset.Printer.render_denotes a.solve.prepareFMI3

noncomputable section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses
open CMemory

/-- Recover the source initialization guarantee from a certificate for the
complete adapter bytes. Calls execute the table printed by those same bytes;
header meanings, native preprocessing and allocated storage remain explicit. -/
theorem adapter_reset_source (compiled : compile input = .ok a)
    (contract : AdapterContract a adapter)
    (heap : Heap) (p : Address) (kind : Kind) (mode : Mode) (t₀ : ℝ)
    (storage : Reset.Storage heap p)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code)) :
    compile input = .ok a ∧ ∃ sigs result,
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      (∀ behavior, (CCalls.Typed.machine (LiteralPreparation.program a.solve.prepareFMI3 sigs)).Behaves
        (.calling "fmi3Reset" [.pointer (some p)] heap .done) behavior ↔
        behavior = .terminates result) ∧ ResetSourceResult a p result t₀ := by
  obtain ⟨sigs, unique, member, printed, _⟩ := contract
  obtain ⟨result, behavior, initialized⟩ := reset_source a
    (LiteralPreparation.program a.solve.prepareFMI3 sigs) heap p kind mode t₀
      (LiteralRejection.function_bound a.solve.prepareFMI3 sigs unique Reset.signature member)
      storage hk hm
  exact ⟨compiled, sigs, result, printed, behavior, initialized⟩

end
end Rumoca.FMI3
