import RumocaC.TokenConcatenation
import RumocaC.FunctionPrinter

/-! The independent CTree grammar separates ordinary string literals. Its
function-text witness is therefore unchanged by every phase-six concatenation
sequence. This does not prove that prior macro/header expansion preserved it. -/
namespace Rumoca.CTree.Syntax
open CTokens.PhaseSix

theorem TypeTokens.nonstring (type : TypeTokens typedefs tokens) :
    ∀ token ∈ tokens, NonString token := by
  induction type with
  | named named => simp [NonString]
  | const type ih => simpa [NonString] using ih
  | volatile type ih => simpa [NonString] using ih
  | pointer type ih =>
      intro token member
      simp only [List.mem_append, List.mem_singleton] at member
      rcases member with member | rfl
      · exact ih token member
      · trivial

theorem Expression.separated (tree : Expression typedefs category tokens expr) : Separated tokens := by
  induction tree using Expression.rec (motive_2 := fun tokens _ _ => Separated tokens) with
  | identifier valid => exact .single _
  | natural value => exact .single _
  | decimalMagnitude => exact .single _
  | decimalNegative =>
      exact (((Separated.single (.number _)).prepend (token := .punctuator "-") trivial).prepend
        (token := .punctuator "(") trivial).append_separator Separated.empty
        (token := .punctuator ")") trivial
  | string => exact .single _
  | widen bound child ih => exact ih
  | parenthesized child ih =>
      simpa using (ih.append_separator .empty (token := .punctuator ")") trivial).prepend
        (token := .punctuator "(") trivial
  | binary rule left right hl hr =>
      simpa using hl.append_separator hr (token := .punctuator _) trivial
  | not child ih => exact ih.prepend trivial
  | dereference child ih => exact ih.prepend trivial
  | address child ih => exact ih.prepend trivial
  | field child valid ih =>
      simpa using ih.append_separator (.single (.word _)) (token := .punctuator ".") trivial
  | pointerField child valid ih =>
      simpa using ih.append_separator (.single (.word _)) (token := .punctuator "->") trivial
  | index base index hb hi =>
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        hb.append_separator (hi.append_separator .empty (token := .punctuator "]") trivial)
          (token := .punctuator "[") trivial
  | callEmpty base ih =>
      simpa using ih.append_separator (.single (.punctuator ")")) (token := .punctuator "(") trivial
  | call base args hb ha =>
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        hb.append_separator (ha.append_separator .empty (token := .punctuator ")") trivial)
          (token := .punctuator "(") trivial
  | cast type child ih =>
      have types := Separated.all_nonstring type.phrase.nonstring
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        (types.append_separator ih (token := .punctuator ")") trivial).prepend
          (token := .punctuator "(") trivial
  | sizeof type =>
      have types := Separated.all_nonstring type.phrase.nonstring
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        ((types.append_separator .empty (token := .punctuator ")") trivial).prepend
          (token := .punctuator "(") trivial).prepend (token := .word "sizeof") trivial
  | one child ih => exact ih
  | cons first rest hf hr =>
      simpa using hf.append_separator hr (token := .punctuator ",") trivial

private theorem assignment_closed (left : Separated lhs) (right : Separated rhs) :
    Closed (lhs ++ [.punctuator "="] ++ rhs ++ [.punctuator ";"]) := by
  apply Closed.seal
  · simpa using left.append_separator right (token := .punctuator "=") trivial
  · trivial

private theorem control_closed (keyword : String) (condition : Separated conditionTokens)
    (body : Closed tokens) :
    Closed ([.word keyword, .punctuator "("] ++ conditionTokens ++ [.punctuator ")", .punctuator "{"] ++
      tokens ++ [.punctuator "}"]) := by
  have block := (Closed.seal body.separated (token := .punctuator "}") trivial).prepend
    (token := .punctuator "{") trivial
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    ((Closed.between condition block (token := .punctuator ")") trivial).prepend
      (token := .punctuator "(") trivial).prepend (token := .word keyword) trivial

theorem BlockItem.closed (item : BlockItem typedefs tokens stmt) : Closed tokens := by
  induction item using BlockItem.rec (motive_2 := fun tokens _ _ => Closed tokens) with
  | declare type name value =>
      rename_i typeText typeTokens declaredName valueTokens expr
      have core := assignment_closed (.single (.word declaredName)) value.separated
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        (Closed.all_nonstring type.phrase.nonstring).append core
  | assign target value => exact assignment_closed target.separated value.separated
  | eval value => exact Closed.seal value.separated trivial
  | returnVoid => exact (Closed.empty.prepend (token := .punctuator ";") trivial).prepend trivial
  | returnValue value =>
      exact (Closed.seal value.separated (token := .punctuator ";") trivial).prepend
        (token := .word "return") trivial
  | ifThen condition yes ih => exact control_closed "if" condition.separated ih
  | ifElse condition yes no hy hn =>
      have first := control_closed "if" condition.separated hy
      have last := ((Closed.seal hn.separated (token := .punctuator "}") trivial).prepend
        (token := .punctuator "{") trivial).prepend (token := .word "else") trivial
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using first.append last
  | whileLoop condition body ih => exact control_closed "while" condition.separated ih
  | nil => exact .empty
  | cons first remaining hf hr => exact hf.append hr

theorem BlockItems.closed (items : BlockItems typedefs tokens stmts) : Closed tokens := by
  induction items using BlockItems.rec (motive_1 := fun _ _ _ => True) with
  | nil => exact .empty
  | cons first remaining ignored ih => exact first.closed.append ih
  | _ => trivial

theorem ParameterPhrase.nonstring (param : ParameterPhrase typedefs tokens value) :
    ∀ token ∈ tokens, NonString token := by
  cases param with
  | scalar type name => simpa [NonString, or_imp, forall_and] using type.phrase.nonstring
  | array type name => simpa [NonString, or_imp, forall_and] using type.phrase.nonstring

theorem ParametersPhrase.nonstring (params : ParametersPhrase typedefs tokens values) :
    ∀ token ∈ tokens, NonString token := by
  induction params with
  | one param => exact param.nonstring
  | cons first remaining ih =>
      simpa [NonString, or_imp, forall_and] using And.intro first.nonstring ih

theorem SignaturePhrase.nonstring (signature : SignaturePhrase typedefs tokens value) :
    ∀ token ∈ tokens, NonString token := by
  cases signature with
  | empty type name => simpa [NonString, or_imp, forall_and] using type.phrase.nonstring
  | params type name params =>
      simpa [NonString, or_imp, forall_and] using And.intro type.phrase.nonstring params.nonstring

theorem FunctionPhrase.closed (function : FunctionPhrase typedefs tokens value) : Closed tokens := by
  cases function with
  | external signature body =>
      have block := (Closed.seal body.closed.separated (token := .punctuator "}") trivial).prepend
        (token := .punctuator "{") trivial
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        (Closed.all_nonstring signature.nonstring).append block
  | internal signature body =>
      have block := (Closed.seal body.closed.separated (token := .punctuator "}") trivial).prepend
        (token := .punctuator "{") trivial
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        ((Closed.all_nonstring signature.nonstring).append block).prepend
          (token := .word "static") trivial

theorem FunctionPhrase.concatenation_unchanged (function : FunctionPhrase typedefs tokens value)
    (steps : Relation.ReflTransGen Rewrite tokens output) : output = tokens :=
  function.closed.separated.unchanged steps

end Rumoca.CTree.Syntax

namespace Rumoca.CTree.Printer

/-- The same lexical witness in an independently read function-text contract
is unchanged by every sequence of ordinary-literal concatenations. This does
not assert that earlier macro expansion left those tokens unchanged. -/
theorem FunctionDenotes.phase_six (contract : FunctionDenotes typedefs text function) :
    ∃ tokens, CTokens.Lexes text.toList tokens ∧ Syntax.FunctionPhrase typedefs tokens function ∧
      ∀ output, Relation.ReflTransGen CTokens.PhaseSix.Rewrite tokens output → output = tokens := by
  obtain ⟨tokens, grammar, lexical⟩ := contract
  exact ⟨tokens, lexical, grammar, fun _ steps => grammar.concatenation_unchanged steps⟩

end Rumoca.CTree.Printer
