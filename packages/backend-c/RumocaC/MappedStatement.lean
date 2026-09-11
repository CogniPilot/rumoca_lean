import RumocaC.StatementOrigins
import RumocaC.MappedExpression

namespace Rumoca.Printed.Document

/-- A right-associated document, using Std's stack-safe list fold. The array
range collector can tail-call through a long sequence of sibling statements. -/
def join (documents : List (Document Origin)) : Document Origin :=
  documents.foldr append (text "")

private theorem string_join_cons (first : String) (rest : List String) :
    String.join (first :: rest) = first ++ String.join rest := by
  have collect : ∀ values : List String, ∀ acc : String,
      values.foldl (fun a b => a ++ b) acc = acc ++ values.foldl (fun a b => a ++ b) "" := by
    intro values
    induction values with
    | nil => intro acc; simp only [List.foldl_nil, String.append_empty]
    | cons value values ih =>
        intro acc
        simp only [List.foldl_cons, String.empty_append]
        rw [ih (acc ++ value), ih value, String.append_assoc]
  simpa only [String.join, List.foldl_cons, String.empty_append] using collect rest first

theorem render_join (documents : List (Document Origin)) :
    (join documents).render = String.join (documents.map render) := by
  induction documents with
  | nil => rfl
  | cons head tail ih =>
      change head.render ++ (join tail).render = String.join ((head :: tail).map render)
      simp only [ih, List.map_cons, string_join_cons]

theorem join_every (documents : List (Document Origin)) (check : Origin → Prop) :
    (join documents).body.EveryOrigin check ↔
      ∀ document ∈ documents, document.body.EveryOrigin check := by
  induction documents with
  | nil => simp [join, text, Doc.EveryOrigin]
  | cons head tail ih =>
      change (head.body.EveryOrigin check ∧ (join tail).body.EveryOrigin check) ↔ _
      simp only [ih, List.mem_cons, forall_eq_or_imp]

/-- Move a conditional outside the length-indexed body before simplifying it. -/
theorem every_if (condition : Prop) [Decidable condition] (yes no : Document Origin)
    (check : Origin → Prop) :
    (if condition then yes else no).body.EveryOrigin check ↔
      if condition then yes.body.EveryOrigin check else no.body.EveryOrigin check := by
  cases ‹Decidable condition› <;> rfl

end Rumoca.Printed.Document

namespace Rumoca.CTree
open Printed
open Printed.Document (text mark)
local infixl:65 " <+> " => Document.append

mutual
def Stmt.Origins.document : {stmt : Stmt} → Stmt.Origins table stmt → Nat → Document (Origin table)
  | .declare type name _, .declare operation typeName declaration value, depth =>
      mark operation (text (String.ofList (List.replicate (2 * depth) ' ')) <+>
        mark typeName (text type) <+> text " " <+> mark declaration (text name) <+>
        text " = " <+> value.document <+> text ";\n")
  | .assign _ _, .assign operation target value, depth =>
      mark operation (text (String.ofList (List.replicate (2 * depth) ' ')) <+>
        target.document <+> text " = " <+> value.document <+> text ";\n")
  | .eval _, .eval operation value, depth =>
      mark operation (text (String.ofList (List.replicate (2 * depth) ' ')) <+>
        value.document <+> text ";\n")
  | .ret none, .retVoid operation, depth =>
      mark operation (text (String.ofList (List.replicate (2 * depth) ' ')) <+> text "return;\n")
  | .ret (some _), .retValue operation value, depth =>
      mark operation (text (String.ofList (List.replicate (2 * depth) ' ')) <+>
        text "return " <+> value.document <+> text ";\n")
  | .branch _ _ whenFalse, .branch operation condition yes no, depth =>
      let indent := text (String.ofList (List.replicate (2 * depth) ' '))
      mark operation (indent <+> text "if (" <+> condition.document <+> text ") {\n" <+>
        Document.join (documents yes (depth + 1) []) <+> indent <+> text "}" <+>
        (if whenFalse.isEmpty then text "\n" else text " else {\n" <+>
          Document.join (documents no (depth + 1) []) <+> indent <+> text "}\n"))
  | .whileLoop _ _, .whileLoop operation condition body, depth =>
      let indent := text (String.ofList (List.replicate (2 * depth) ' '))
      mark operation (indent <+> text "while (" <+> condition.document <+> text ") {\n" <+>
        Document.join (documents body (depth + 1) []) <+> indent <+> text "}\n")

/-- Build a list with a reverse accumulator. No recursive call stack grows
with the number of sibling statements; Std supplies the final reverse. -/
def Stmt.Origins.documents : OriginList (Stmt.Origins table) statements → Nat →
    List (Document (Origin table)) → List (Document (Origin table))
  | .nil, _, acc => acc.reverse
  | .cons head tail, depth, acc => documents tail depth (head.document depth :: acc)
end

mutual
theorem Stmt.Origins.document_render (origins : Stmt.Origins table stmt) (depth : Nat) :
    (origins.document depth).render = stmt.render depth := by
  cases origins with
  | declare | assign | eval | retVoid | retValue =>
      simp only [document, Document.render_mark, Document.render_append, Document.render_text,
        Expr.Origins.document_render, Stmt.render]
  | branch operation condition yes no =>
      simp only [document, Document.render_mark, Document.render_append, Document.render_text,
        Expr.Origins.document_render, Document.render_join, documents_render yes,
        List.reverse_nil, List.map_nil, List.nil_append, Stmt.render]
      split <;> simp only [Document.render_text, Document.render_append, Document.render_join,
        documents_render no, List.reverse_nil, List.map_nil, List.nil_append]
  | whileLoop operation condition body =>
      simp only [document, Document.render_mark, Document.render_append, Document.render_text,
        Expr.Origins.document_render, Document.render_join, documents_render body,
        List.reverse_nil, List.map_nil, List.nil_append, Stmt.render]

theorem Stmt.Origins.documents_render (origins : OriginList (Stmt.Origins table) statements)
    (depth : Nat) (acc : List (Document (Origin table))) :
    (documents origins depth acc).map Document.render =
      acc.reverse.map Document.render ++ statements.map (fun stmt => stmt.render depth) := by
  cases origins with
  | nil => simp only [documents, List.map_nil, List.append_nil]
  | cons head tail =>
      simp only [documents, documents_render tail, List.reverse_cons, List.map_append,
        List.map_cons, List.map_nil, document_render head, List.append_assoc,
        List.cons_append, List.nil_append]
end

theorem Stmt.Origins.root_region (origins : Stmt.Origins table stmt) (depth : Nat) :
    Region (origins.document depth).body origins.root "" (stmt.render depth) "" := by
  rw [← origins.document_render depth]
  cases origins <;> simp only [document, Document.mark, Document.render, root] <;>
    exact .here _ _

mutual
theorem Stmt.Origins.document_every (origins : Stmt.Origins table stmt) (depth : Nat)
    (check : Origin table → Prop) :
    (origins.document depth).body.EveryOrigin check ↔ origins.Every check := by
  cases origins with
  | declare | assign | eval | retVoid | retValue =>
      simp only [document, Document.mark, Document.text, Document.append, Doc.EveryOrigin,
        Expr.Origins.document_every, Every, true_and, and_true, and_assoc]
  | branch operation condition yes no =>
      cases no with
      | nil =>
          simp only [document, Document.every_if, List.isEmpty_nil, eq_self, ↓reduceIte, Document.mark, Document.text,
            Document.append, Doc.EveryOrigin, Document.join_every,
            documents_every yes (depth + 1) [] check, Expr.Origins.document_every,
            Every, EveryList, List.not_mem_nil, false_implies, implies_true,
            true_and, and_true]
      | cons head tail =>
          simp only [document, Document.every_if, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, Document.mark, Document.text,
            Document.append, Doc.EveryOrigin, Document.join_every,
            documents_every yes (depth + 1) [] check,
            documents_every (.cons head tail) (depth + 1) [] check,
            Expr.Origins.document_every, Every, List.not_mem_nil, false_implies,
            implies_true, true_and, and_true, and_assoc]
  | whileLoop operation condition body =>
      simp only [document, Document.mark, Document.text, Document.append, Doc.EveryOrigin,
        Document.join_every, documents_every body (depth + 1) [] check,
        Expr.Origins.document_every, Every, List.not_mem_nil, false_implies,
        implies_true, true_and, and_true]

theorem Stmt.Origins.documents_every (origins : OriginList (Stmt.Origins table) statements)
    (depth : Nat) (acc : List (Document (Origin table))) (check : Origin table → Prop) :
    (∀ document ∈ documents origins depth acc, document.body.EveryOrigin check) ↔
      (∀ document ∈ acc, document.body.EveryOrigin check) ∧ EveryList check origins := by
  cases origins with
  | nil => simp only [documents, List.mem_reverse, EveryList, and_true]
  | cons head tail =>
      simp only [documents, documents_every tail depth _ check, List.mem_cons,
        forall_eq_or_imp, document_every head depth check, EveryList,
        and_assoc, and_left_comm]
end

theorem Stmt.Origins.map_exact (origins : Stmt.Origins table stmt) (depth : Nat)
    (entry : Entry (Origin table)) :
    entry ∈ (origins.document depth).entries ↔
    ∃ beforeText segment suffix,
      Region (origins.document depth).body entry.origin beforeText segment suffix ∧
      stmt.render depth = beforeText ++ segment ++ suffix ∧
      entry.start = beforeText.utf8ByteSize ∧
      entry.stop = entry.start + segment.utf8ByteSize ∧
      (stmt.render depth).toByteArray.extract entry.start entry.stop = segment.toByteArray := by
  constructor
  · intro member
    obtain ⟨beforeText, segment, suffix, region, first, last⟩ :=
      ((origins.document depth).body.map_iff entry).mp member
    refine ⟨beforeText, segment, suffix, region,
      (origins.document_render depth).symm.trans region.render_eq, first, last, ?_⟩
    rw [← origins.document_render depth, last, first]
    exact region.bytes
  · rintro ⟨beforeText, segment, suffix, region, _, first, last, _⟩
    exact ((origins.document depth).body.map_iff entry).mpr
      ⟨beforeText, segment, suffix, region, first, last⟩

theorem Stmt.Origins.map_every (origins : Stmt.Origins table stmt) (depth : Nat)
    (check : Origin table → Prop) (checked : origins.Every check)
    (entry : Entry (Origin table)) (member : entry ∈ (origins.document depth).entries) :
    check entry.origin :=
  (origins.document depth).body.map_every check
    ((origins.document_every depth check).mpr checked) entry member

end Rumoca.CTree
