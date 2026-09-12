import Rumoca.FMI3ResetProofs
import Rumoca.FMI3NameProofs
import RumocaFMI3.AdapterPreprocessing
import RumocaFMI3.AdapterPrinter
import RumocaFMI3.CallTypes
import RumocaFMI3.CountContract
import RumocaFMI3.Version

/-! Complete adapter byte identity, independent function-section grammar and
typed public/helper call entry, together with the reset execution/source consequence. Other function execution,
whole-C preprocessing, scope/types, official-header meanings and native ABI remain
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
    AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
    (∀ fn ∈ LiteralPreparation.functions a.solve.prepareFMI3 sigs,
      @CCalls.Signature.Ready cInterface fn.signature) ∧
    (∀ static : StaticLiterals,
      @Reset.FunctionContract static a.parsed.ast a.solve.prepareFMI3
        (Runtime.function a.solve.prepareFMI3 Reset.signature).render) ∧
    (∀ (static : StaticLiterals) (events : Bool),
      @CountQueries.FunctionContract static a.parsed.ast a.solve.prepareFMI3 sigs events
        (Runtime.function a.solve.prepareFMI3 (CountQueries.signature events)).render) ∧
    (LiteralPreparation.prepare a.solve.prepareFMI3 sigs).isSome = true ∧
    Version.FunctionContract a.solve.prepareFMI3 sigs
      (Runtime.function a.solve.prepareFMI3 Version.signature).render

theorem adapter_correct (a : Artifact input) (sigs : List CTree.Signature)
    (unique : ((LiteralPreparation.functions a.solve.prepareFMI3 sigs).map
      (fun fn => fn.signature.name)).Nodup)
    (member : Reset.signature ∈ sigs)
    (spellings : ∀ sig ∈ sigs, CTree.Preprocessing.SignatureInputs sig)
    (grammar : ∀ sig ∈ sigs, CTree.Printer.SignaturePrintable RuntimePrinter.typedefs sig)
    (ready : ∀ sig ∈ sigs, @CCalls.Signature.Ready cInterface sig)
    (counts : ∀ events, CountQueries.signature events ∈ sigs)
    (version : Version.signature ∈ sigs)
    (pool : (LiteralPreparation.prepare a.solve.prepareFMI3 sigs).isSome = true)
    (printed : Runtime.render a.solve.prepareFMI3 sigs = adapter) : AdapterContract a adapter :=
  ⟨sigs, unique, member, printed,
    printed ▸ AdapterPreprocessing.render_stable a.solve.prepareFMI3 sigs
      (AdapterPreprocessing.name_plain (parsed_name a.parsed)) spellings,
    printed ▸ AdapterPrinter.rendered_contract a.solve.prepareFMI3 sigs grammar,
    CallTypes.functions_ready a.solve.prepareFMI3 sigs ready _,
    (fun _ => Reset.rendered_contract _),
    (fun _ events => CountQueries.rendered_contract _ sigs events unique (counts events)), pool,
    Version.rendered_contract _ sigs unique version⟩

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
  obtain ⟨sigs, unique, member, printed, stable, functions, _, reset, _, _, _⟩ := contract
  obtain ⟨before, after, located⟩ := LiteralPreparation.rendered_member a.solve.prepareFMI3 sigs Reset.signature member
  refine ⟨before, (Runtime.function a.solve.prepareFMI3 Reset.signature).render, after,
    printed ▸ located, ?_⟩
  exact Reset.Printer.render_denotes a.solve.prepareFMI3

/-- Normal-context maximal tokenization and ordinary-string concatenation use
the same grammar witness for the reset fragment located in the actual file.
This retains the containing adapter's prior byte, character and call contract;
preprocessing directives, headers and the other public functions remain open. -/
theorem adapter_reset_tokenization (contract : AdapterContract a adapter) :
    ∃ before text after : String,
      adapter = before ++ text ++ after ∧
      CTree.Printer.FunctionTokenization Reset.Printer.typedefs text
        (Runtime.function a.solve.prepareFMI3 Reset.signature) := by
  obtain ⟨before, text, after, located, grammar⟩ := adapter_reset_syntax contract
  exact ⟨before, text, after, located, grammar.tokenization⟩

/-- The actual file's complete function section denotes the same definition
table retained by the execution contract. Maximal tokenization and ordinary
literal concatenation share its per-function grammar witnesses. The preamble's
headers, directives and declarations still require separate interpretation. -/
theorem adapter_functions_tokenization (contract : AdapterContract a adapter) :
    ∃ sigs, Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter := by
  obtain ⟨sigs, _, _, printed, _, functions, _⟩ := contract
  exact ⟨sigs, printed, functions⟩

noncomputable section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses
open CMemory

/-- Every function in the actual adapter has at least one convertible argument
list. All convertible lists enter its exact body with a fresh coherent scope,
the caller's unchanged heap and continuation. This is entry, not a claim about
termination, effects of the body, pointer storage, callbacks or native ABI. -/
theorem adapter_call_entry (contract : AdapterContract a adapter) :
    ∃ sigs,
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      (∀ fn ∈ LiteralPreparation.functions a.solve.prepareFMI3 sigs,
        ∃ values, CCalls.Signature.Arguments fn.signature.parameters values values) ∧
      ∀ fn ∈ LiteralPreparation.functions a.solve.prepareFMI3 sigs,
        ∀ inputs outputs heap stack,
          CCalls.Signature.Arguments fn.signature.parameters inputs outputs →
          ∃ types,
            CCalls.Typed.next (LiteralPreparation.program a.solve.prepareFMI3 sigs)
              (.calling fn.signature.name inputs heap stack) =
              some (.body (.running fn.body
                (CCalls.Signature.locals fn.signature.parameters outputs) types heap)
                fn.signature.result stack) ∧
            CCalls.Parameters.Coherent
              (CCalls.Signature.locals fn.signature.parameters outputs) types := by
  obtain ⟨sigs, unique, _, printed, _, functions, ready, _⟩ := contract
  refine ⟨sigs, printed, functions, ?_, ?_⟩
  · exact CallTypes.arguments_exist a.solve.prepareFMI3 sigs ready static.addresses
  · intro fn member inputs outputs heap stack arguments
    exact CallTypes.entry a.solve.prepareFMI3 sigs unique ready static.addresses
      fn member arguments heap stack

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
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      (∀ behavior, (CCalls.Typed.machine (LiteralPreparation.program a.solve.prepareFMI3 sigs)).Behaves
        (.calling "fmi3Reset" [.pointer (some p)] heap .done) behavior ↔
        behavior = .terminates result) ∧ ResetSourceResult a p result t₀ := by
  obtain ⟨sigs, unique, member, printed, _, functions, _⟩ := contract
  obtain ⟨result, behavior, initialized⟩ := reset_source a
    (LiteralPreparation.program a.solve.prepareFMI3 sigs) heap p kind mode t₀
      (LiteralPreparation.function_bound a.solve.prepareFMI3 sigs unique Reset.signature member)
      storage hk hm
  exact ⟨compiled, sigs, result, printed, functions, behavior, initialized⟩

end
end Rumoca.FMI3
