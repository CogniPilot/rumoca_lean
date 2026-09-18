import RumocaC.Origins
import RumocaC.SourceMap

namespace Rumoca.Printed

/-- A document with its cached byte length available at composition boundaries. -/
structure Document (Origin : Type) where
  size : Nat
  body : Doc Origin size

namespace Document
def text (value : String) : Document Origin := ⟨_, .text value⟩
def append (left right : Document Origin) : Document Origin :=
  ⟨left.size + right.size, .append left.body right.body⟩
def mark (origin : Origin) (body : Document Origin) : Document Origin :=
  ⟨body.size, .mark origin body.body⟩
def render (document : Document Origin) : String := document.body.render
def entries (document : Document Origin) : Array (Entry Origin) :=
  document.body.entriesInto 0 #[]

@[simp] theorem body_render (document : Document Origin) : document.body.render = document.render := rfl
@[simp] theorem render_text (value : String) : (text (Origin := Origin) value).render = value := rfl
@[simp] theorem render_append (left right : Document Origin) :
    (left.append right).render = left.render ++ right.render := rfl
@[simp] theorem render_mark (origin : Origin) (body : Document Origin) :
    (mark origin body).render = body.render := rfl
end Document
end Rumoca.Printed

namespace Rumoca.CTree
open Printed
open Printed.Document (text mark)
local infixl:65 " <+> " => Document.append

mutual
def Expr.Origins.document : {expr : Expr} → Expr.Origins table expr → Document (Origin table)
  | .id name, .id origin => mark origin (text name)
  | .nat value, .nat origin => mark origin (text (toString value))
  | .decimal negative mantissa exponent, .decimal origin =>
      mark origin (text (Expr.render (.decimal negative mantissa exponent)))
  | .str value, .str origin => mark origin (text (quote value))
  | .bin op _ _, .bin origin left right =>
      mark origin (text "(" <+> left.document <+> text " " <+> text op.render <+>
        text " " <+> right.document <+> text ")")
  | .not _, .not origin value => mark origin (text "(!" <+> value.document <+> text ")")
  | .deref _, .deref origin value => mark origin (text "(*" <+> value.document <+> text ")")
  | .address _, .address origin value => mark origin (text "(&" <+> value.document <+> text ")")
  | .field _ name pointer, .field origin member value =>
      mark origin (text "(" <+> value.document <+> text (if pointer then "->" else ".") <+>
        mark member (text name) <+> text ")")
  | .index _ _, .index origin base offset =>
      mark origin (base.document <+> text "[" <+> offset.document <+> text "]")
  | .call _ _, .call origin callee arguments =>
      mark origin (callee.document <+> text "(" <+> argumentsDocument arguments <+> text ")")
  | .cast type _, .cast origin typeName value =>
      mark origin (text "((" <+> mark typeName (text type) <+> text ")" <+>
        value.document <+> text ")")
  | .sizeof type, .sizeof origin typeName =>
      mark origin (text "sizeof(" <+> mark typeName (text type) <+> text ")")

def Expr.Origins.argumentsDocument : OriginList (Expr.Origins table) args → Document (Origin table)
  | .nil => text ""
  | .cons head tail => argumentsDocumentTail tail head.document

def Expr.Origins.argumentsDocumentTail : OriginList (Expr.Origins table) args →
    Document (Origin table) → Document (Origin table)
  | .nil, acc => acc
  | .cons head tail, acc => argumentsDocumentTail tail (acc <+> text ", " <+> head.document)
end

mutual
/-- The mapped printer emits exactly the established C printer's bytes for
every existing expression and every complete origin annotation. -/
theorem Expr.Origins.document_render (origins : Expr.Origins table expr) :
    origins.document.render = expr.render := by
  cases origins with
  | id | nat | decimal | str | sizeof => simp only [document, Document.render_mark,
      Document.render_append, Document.render_text, Expr.render]
  | bin origin left right | index origin left right =>
      simp only [document, Document.render_mark, Document.render_append, Document.render_text,
        document_render left, document_render right, Expr.render]
  | not origin value | deref origin value | address origin value =>
      simp only [document, Document.render_mark, Document.render_append, Document.render_text,
        document_render value, Expr.render]
  | field origin member value | cast origin member value =>
      simp only [document, Document.render_mark, Document.render_append, Document.render_text,
        document_render value, Expr.render]
  | call origin callee arguments =>
      simp only [document, Document.render_mark, Document.render_append, Document.render_text,
        document_render callee, argumentsDocument_render arguments, Expr.render]

theorem Expr.Origins.argumentsDocument_render (origins : OriginList (Expr.Origins table) args) :
    (argumentsDocument origins).render = String.intercalate ", " (args.map Expr.render) := by
  cases origins with
  | nil => rfl
  | cons head tail =>
      simp only [argumentsDocument, argumentsDocumentTail_render, document_render,
        List.map_cons]

theorem Expr.Origins.argumentsDocumentTail_render (origins : OriginList (Expr.Origins table) args)
    (acc : Document (Origin table)) :
    (argumentsDocumentTail origins acc).render =
      String.intercalate ", " (acc.render :: args.map Expr.render) := by
  cases origins with
  | nil => rfl
  | cons head tail =>
      simp only [argumentsDocumentTail, argumentsDocumentTail_render tail,
        Document.render_append, Document.render_text, document_render head,
        List.map_cons]
      rfl
end

theorem Expr.Origins.root_region (origins : Expr.Origins table expr) :
    Printed.Region origins.document.body origins.root "" expr.render "" := by
  rw [← origins.document_render]
  cases origins <;> simp only [document, Document.mark, Document.render, root] <;>
    exact .here _ _

theorem Expr.Origins.map_exact (origins : Expr.Origins table expr)
    (entry : Printed.Entry (Origin table)) (member : entry ∈ origins.document.entries) :
    ∃ beforeText segment suffix,
      Printed.Region origins.document.body entry.origin beforeText segment suffix ∧
      expr.render = beforeText ++ segment ++ suffix ∧
      entry.start = beforeText.utf8ByteSize ∧
      entry.stop = entry.start + segment.utf8ByteSize := by
  obtain ⟨beforeText, segment, suffix, region, first, last⟩ :=
    (origins.document.body.map_iff entry).mp member
  exact ⟨beforeText, segment, suffix, region,
    origins.document_render.symm.trans region.render_eq, first, last⟩

mutual
/-- No annotated expression origin is lost or invented by the document
construction. This equivalence holds for any predicate on origin references. -/
theorem Expr.Origins.document_every (origins : Expr.Origins table expr)
    (check : Origin table → Prop) :
    origins.document.body.EveryOrigin check ↔ origins.Every check := by
  cases origins with
  | id | nat | decimal | str | sizeof =>
      simp only [document, Document.mark, Document.text, Document.append, Doc.EveryOrigin,
        Every, and_true, true_and]
  | bin origin left right | index origin left right =>
      simp only [document, Document.mark, Document.text, Document.append, Doc.EveryOrigin,
        document_every left, document_every right, Every, and_true, true_and]
  | not origin value | deref origin value | address origin value =>
      simp only [document, Document.mark, Document.text, Document.append, Doc.EveryOrigin,
        document_every value, Every, and_true, true_and]
  | field origin member value | cast origin member value =>
      simp only [document, Document.mark, Document.text, Document.append, Doc.EveryOrigin,
        document_every value, Every, true_and, and_comm]
  | call origin callee arguments =>
      simp only [document, Document.mark, Document.text, Document.append, Doc.EveryOrigin,
        document_every callee, argumentsDocument_every arguments, Every, and_true]

theorem Expr.Origins.argumentsDocument_every (origins : OriginList (Expr.Origins table) args)
    (check : Origin table → Prop) :
    (argumentsDocument origins).body.EveryOrigin check ↔ EveryList check origins := by
  cases origins with
  | nil => simp only [argumentsDocument, Document.text, Doc.EveryOrigin, EveryList]
  | cons head tail =>
      simp only [argumentsDocument, argumentsDocumentTail_every tail head.document check,
        document_every head check, EveryList]

theorem Expr.Origins.argumentsDocumentTail_every (origins : OriginList (Expr.Origins table) args)
    (acc : Document (Origin table)) (check : Origin table → Prop) :
    (argumentsDocumentTail origins acc).body.EveryOrigin check ↔
      acc.body.EveryOrigin check ∧ EveryList check origins := by
  cases origins with
  | nil => simp only [argumentsDocumentTail, EveryList, and_true]
  | cons head tail =>
      simp only [argumentsDocumentTail, argumentsDocumentTail_every tail,
        Document.append, Document.text, Doc.EveryOrigin, document_every head,
        EveryList, and_true, and_assoc]
end

end Rumoca.CTree
