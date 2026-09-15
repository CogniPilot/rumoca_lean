import RumocaFMI3.EventIndicatorEnvironment
import RumocaFMI3.RuntimePrinter

noncomputable section
namespace Rumoca.FMI3.EventIndicatorCalls
open CTree CMemory CLiteral

/-- FMI 3.0.2 §§2.3.3, 2.3.5, 2.3.8 and 3.2.1 admit this
value query for ME in these modes. Prose-to-predicate correspondence is
a standards review obligation, separate from the following equivalence. -/
def Allowed (kind : Kind) (mode : Mode) : Prop :=
  kind = .me ∧
    (mode = .initialization ∨ mode = .event ∨ mode = .continuous ∨ mode = .terminated)

theorem allowed_iff (kind : Kind) (mode : Mode) :
    Allowed kind mode ↔ Reference.Allowed .getDerivatives kind mode := Iff.rfl

/-- A valid empty query preserves the entire heap. Passing a null output
pointer is additional defensive behavior of the authored body, not a claim
that FMI's general argument rule requires importers to pass null. -/
theorem QuietContract.get_refines {E : Type} [CInterface]
    {program : CCalls.Events.Program E} {heap : Heap}
    (contract : QuietContract program heap) (p : Address) (buffer : Option Address)
    (kind : Kind) (mode : Mode)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Allowed kind mode) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling signature.name (values (some p) buffer 0) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, heap⟩ := by
  obtain ⟨rfl, modes⟩ := allowed
  exact contract.get p buffer mode hk hm ⟨rfl, modes⟩ behavior

/-- Printed C and prepared execution use the same actual function table.
Numerical helpers are unnecessary: the admitted product has no event output
elements. Actual XML and complete-file binding belong to the source theorem. -/
structure FunctionContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (text : String) : Prop where
  member : signature ∈ sigs
  printed : text = (Runtime.function model signature).render
  tokenization : Printer.FunctionTokenization RuntimePrinter.typedefs text
    (Runtime.function model signature)
  runtime : ∀ pool, LiteralPreparation.prepare model sigs = some pool →
    EventIndicatorEnvironment.PreparedContract model sigs pool

theorem rendered_contract (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature ∈ sigs) :
    FunctionContract model sigs (Runtime.function model signature).render := by
  refine ⟨member, rfl, ?_,
    fun _ made => EventIndicatorEnvironment.prepared_correct model sigs unique member made⟩
  apply RuntimePrinter.function_tokenization
  refine ⟨Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)),
    by decide +kernel, ?_⟩
  intro param member
  simp only [signature, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals exact ⟨Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)),
    by decide +kernel⟩

end Rumoca.FMI3.EventIndicatorCalls
end
