import RumocaC.FunctionOrigins
import RumocaC.MappedStatement

/-! Complete function maps for existing C syntax. These proofs identify actual
printer bytes and all supplied annotations; backend-owned rule/source
correspondence, C validity and execution are independent requirements. -/
namespace Rumoca.CTree
open Printed
open Printed.Document (text mark)
local infixl:65 " <+> " => Document.append

def Parameter.Origins.document (origins : Parameter.Origins table parameter) : Document (Origin table) :=
  mark origins.declaration (mark origins.typeName (text parameter.type) <+> text " " <+>
    mark origins.name (text parameter.name) <+> text (if parameter.array then "[]" else ""))

theorem Parameter.Origins.document_render (origins : Parameter.Origins table parameter) :
    origins.document.render = parameter.render := by
  simp only [document, Document.render_mark, Document.render_append, Document.render_text,
    Parameter.render]

theorem Parameter.Origins.document_every (origins : Parameter.Origins table parameter)
    (check : Origin table → Prop) :
    origins.document.body.EveryOrigin check ↔ origins.Every check := by
  simp only [document, Document.mark, Document.append, Document.text, Doc.EveryOrigin,
    Every, and_true]

def Parameter.Origins.documentsTail : OriginList (Parameter.Origins table) parameters →
    Document (Origin table) → Document (Origin table)
  | .nil, acc => acc
  | .cons head tail, acc => documentsTail tail (acc <+> text ", " <+> head.document)

def Parameter.Origins.documents : OriginList (Parameter.Origins table) parameters → Document (Origin table)
  | .nil => text "void"
  | .cons head tail => documentsTail tail head.document

theorem Parameter.Origins.documentsTail_render
    (origins : OriginList (Parameter.Origins table) parameters) (acc : Document (Origin table)) :
    (documentsTail origins acc).render =
      String.intercalate ", " (acc.render :: parameters.map Parameter.render) := by
  induction origins generalizing acc with
  | nil => rfl
  | cons head tail ih =>
      simp only [documentsTail, ih, Document.render_append, Document.render_text,
        document_render, List.map_cons]
      rfl

theorem Parameter.Origins.documents_render (origins : OriginList (Parameter.Origins table) parameters) :
    (documents origins).render =
      if parameters.isEmpty then "void" else String.intercalate ", " (parameters.map Parameter.render) := by
  cases origins with
  | nil => rfl
  | cons head tail =>
      simp only [documents, documentsTail_render, document_render, List.isEmpty_cons,
        Bool.false_eq_true, ↓reduceIte, List.map_cons]

theorem Parameter.Origins.documentsTail_every
    (origins : OriginList (Parameter.Origins table) parameters) (acc : Document (Origin table))
    (check : Origin table → Prop) :
    (documentsTail origins acc).body.EveryOrigin check ↔
      acc.body.EveryOrigin check ∧ EveryList check origins := by
  induction origins generalizing acc with
  | nil => simp only [documentsTail, EveryList, and_true]
  | cons head tail ih =>
      simp only [documentsTail, ih, Document.append, Document.text, Doc.EveryOrigin,
        document_every, EveryList, and_true, and_assoc]

theorem Parameter.Origins.documents_every (origins : OriginList (Parameter.Origins table) parameters)
    (check : Origin table → Prop) :
    (documents origins).body.EveryOrigin check ↔ EveryList check origins := by
  cases origins with
  | nil => rfl
  | cons head tail => simp only [documents, documentsTail_every, document_every, EveryList]

def Signature.Origins.document (origins : Signature.Origins table signature) : Document (Origin table) :=
  mark origins.declaration (mark origins.resultType (text signature.result) <+> text " " <+>
    mark origins.name (text signature.name) <+> text "(" <+>
    Parameter.Origins.documents origins.parameters <+> text ")")

theorem Signature.Origins.document_render (origins : Signature.Origins table signature) :
    origins.document.render = signature.render := by
  simp only [document, Document.render_mark, Document.render_append, Document.render_text,
    Parameter.Origins.documents_render, Signature.render]

theorem Signature.Origins.document_every (origins : Signature.Origins table signature)
    (check : Origin table → Prop) :
    origins.document.body.EveryOrigin check ↔ origins.Every check := by
  simp only [document, Document.mark, Document.append, Document.text, Doc.EveryOrigin,
    Parameter.Origins.documents_every, Every, and_true, and_assoc]

def Function.Origins.document (origins : Function.Origins table function) : Document (Origin table) :=
  mark origins.definition (text (if function.static then "static " else "") <+>
    origins.signature.document <+> text " {\n" <+>
    Document.join (Stmt.Origins.documents origins.body 1 []) <+> text "}\n\n")

theorem Function.Origins.document_render (origins : Function.Origins table function) :
    origins.document.render = function.render := by
  simp only [document, Document.render_mark, Document.render_append, Document.render_text,
    Signature.Origins.document_render, Document.render_join, Stmt.Origins.documents_render,
    List.reverse_nil, List.map_nil, List.nil_append, Function.render]

theorem Function.Origins.document_every (origins : Function.Origins table function)
    (check : Origin table → Prop) :
    origins.document.body.EveryOrigin check ↔ origins.Every check := by
  simp only [document, Document.mark, Document.append, Document.text, Doc.EveryOrigin,
    Signature.Origins.document_every, Document.join_every,
    Stmt.Origins.documents_every, Every, List.not_mem_nil, false_implies,
    implies_true, true_and, and_true]

theorem Function.Origins.root_region (origins : Function.Origins table function) :
    Region origins.document.body origins.definition "" function.render "" := by
  rw [← origins.document_render]
  exact .here _ _

theorem Function.Origins.map_exact (origins : Function.Origins table function)
    (entry : Entry (Origin table)) :
    entry ∈ origins.document.entries ↔
    ∃ beforeText segment suffix,
      Region origins.document.body entry.origin beforeText segment suffix ∧
      function.render = beforeText ++ segment ++ suffix ∧
      entry.start = beforeText.utf8ByteSize ∧
      entry.stop = entry.start + segment.utf8ByteSize ∧
      function.render.toByteArray.extract entry.start entry.stop = segment.toByteArray := by
  constructor
  · intro member
    obtain ⟨beforeText, segment, suffix, region, first, last⟩ := (origins.document.body.map_iff entry).mp member
    refine ⟨beforeText, segment, suffix, region, origins.document_render.symm.trans region.render_eq,
      first, last, ?_⟩
    rw [← origins.document_render, last, first]
    exact region.bytes
  · rintro ⟨beforeText, segment, suffix, region, _, first, last, _⟩
    exact (origins.document.body.map_iff entry).mpr ⟨beforeText, segment, suffix, region, first, last⟩

theorem Function.Origins.map_every (origins : Function.Origins table function)
    (check : Origin table → Prop) (checked : origins.Every check)
    (entry : Entry (Origin table)) (member : entry ∈ origins.document.entries) : check entry.origin :=
  origins.document.body.map_every check ((origins.document_every check).mpr checked) entry member

end Rumoca.CTree
