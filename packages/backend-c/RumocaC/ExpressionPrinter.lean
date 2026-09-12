import RumocaC.ExpressionSyntax
import RumocaC.TreeBoundary
import RumocaC.TextLemmas

/-! Compositional character-to-grammar contracts for the actual CTree expression
printer. The domain distinguishes a raw construction tree from syntax-valid C.
Type compatibility, evaluation order, scopes and execution remain separate. -/
namespace Rumoca.CTree.Printer
open Syntax CTokens

def Postfix (expr : Expr) : Prop := match expr with
  | .sizeof _ => False
  | _ => True

def FieldBase (expr : Expr) : Prop := match expr with
  | .nat _ => False
  | _ => True

/-- Only bare words/numbers can absorb a following character. Every other
expression emitted by CTree ends with a closing punctuator or a quoted token. -/
def TailSafe : Expr → Char → Prop
  | .id _, marker => CLexical.identifierCharacter marker = false ∧ marker ≠ '"' ∧ marker ≠ '\''
  | .nat _, marker => CPPNumber.character marker = false
  | _, _ => True

structure Derivation (typedefs : List String) (expr : Expr) (tokens : List CTokens.Token) : Prop where
  unary : Expression typedefs .unary tokens expr
  asPostfix : Postfix expr → Expression typedefs .postfix tokens expr

def Renders (typedefs : List String) (expr : Expr) : Prop :=
  ∃ tokens, Derivation typedefs expr tokens ∧
    ∀ marker rest, TailSafe expr marker →
      CTokens.Prefix (expr.render.toList ++ marker :: rest) tokens (marker :: rest)

private theorem of_primary (tree : Expression typedefs .primary tokens expr) :
    Derivation typedefs expr tokens :=
  ⟨.widen (by decide +kernel) tree, fun _ => .widen (by decide +kernel) tree⟩

private theorem of_postfix (tree : Expression typedefs .postfix tokens expr) :
    Derivation typedefs expr tokens :=
  ⟨.widen (by decide +kernel) tree, fun _ => tree⟩

theorem tail_safe_separator (expr : Expr) (member : marker ∈ [' ', ')', ']', ';', ',', '[', '(']) :
    TailSafe expr marker := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  cases expr <;> rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [TailSafe] <;> decide +kernel

open CTokens (separator_prefix)

private theorem operator_prefix (op : BinOp) (rest : List Char) :
    CTokens.Prefix (op.render.toList ++ ' ' :: rest) [.punctuator op.render] (' ' :: rest) := by
  apply CTokens.punctuator_prefix (CPunctuator.binop_consumes op rest)
  cases op <;> simp [BinOp.render, CTokens.PunctuationSafe]

theorem identifier_renders (valid : CIdentifier.valid typedefs name = true) :
    Renders typedefs (.id name) := by
  refine ⟨[.word name], of_primary (.identifier valid), ?_⟩
  intro marker rest safe
  simpa only [Expr.render] using CTokens.word_prefix
    (CIdentifier.word_parts typedefs name valid) safe.1 safe.2.1 safe.2.2 rest

theorem natural_renders (n : Nat) : Renders typedefs (.nat n) := by
  refine ⟨[.number (toString n)], of_primary (.natural (CDecimal.render_denotes n)), ?_⟩
  intro marker rest safe
  simpa only [Expr.render] using CTokens.natural_prefix n safe rest

theorem string_renders (value : String) : Renders typedefs (.str value) := by
  refine ⟨[.string (value.toUTF8.data.toList ++ [0])], of_primary .string, ?_⟩
  intro marker rest safe
  simpa only [Expr.render] using CTokens.string_prefix value (marker :: rest)

theorem binary_renders (op : BinOp) (left : Renders typedefs a) (right : Renders typedefs b) :
    Renders typedefs (.bin op a b) := by
  obtain ⟨leftTokens, leftGrammar, leftLex⟩ := left
  obtain ⟨rightTokens, rightGrammar, rightLex⟩ := right
  refine ⟨.punctuator "(" :: (leftTokens ++ [.punctuator op.render] ++ rightTokens) ++ [.punctuator ")"],
    of_primary (Expression.binary_grouped op
      (.widen (by decide +kernel) leftGrammar.unary) (.widen (by decide +kernel) rightGrammar.unary)), ?_⟩
  intro marker rest safe
  have close := separator_prefix (spelling := ")") (by simp) (marker :: rest)
  have rhs := rightLex ')' (marker :: rest) (tail_safe_separator b (by simp))
  have afterOperator : CTokens.Prefix (' ' :: (b.render.toList ++ ')' :: marker :: rest))
      (rightTokens ++ [.punctuator ")"]) (marker :: rest) :=
    .space (by decide +kernel) (rhs.append close)
  have operator := operator_prefix op (b.render.toList ++ ')' :: marker :: rest)
  have afterLeft : CTokens.Prefix
      (' ' :: (op.render.toList ++ ' ' :: (b.render.toList ++ ')' :: marker :: rest)))
      ([.punctuator op.render] ++ rightTokens ++ [.punctuator ")"]) (marker :: rest) := by
    simpa only [List.append_assoc] using
      CTokens.Prefix.space (by decide +kernel) (operator.append afterOperator)
  have lhs := leftLex ' ' (op.render.toList ++ ' ' :: (b.render.toList ++ ')' :: marker :: rest))
    (tail_safe_separator a (by simp))
  have openParen := separator_prefix (spelling := "(") (by simp)
    (a.render.toList ++ ' ' :: (op.render.toList ++ ' ' :: (b.render.toList ++ ')' :: marker :: rest)))
  simpa only [Expr.render, String.toList_append, List.append_assoc, List.cons_append, List.nil_append] using
    openParen.append (lhs.append afterLeft)

inductive UnaryForm : (Expr → Expr) → String → Prop where
  | not : UnaryForm Expr.not "!"
  | dereference : UnaryForm Expr.deref "*"
  | address : UnaryForm Expr.address "&"

private theorem UnaryForm.expression (form : UnaryForm make spelling)
    (child : Expression typedefs .cast tokens expr) :
    Expression typedefs .unary (.punctuator spelling :: tokens) (make expr) := by
  cases form with
  | not => exact .not child
  | dereference => exact .dereference child
  | address => exact .address child

private theorem UnaryForm.printed (form : UnaryForm make spelling) (expr : Expr) :
    (make expr).render = "(" ++ spelling ++ expr.render ++ ")" := by
  cases form <;> simp only [Expr.render] <;> rfl

theorem unary_renders (form : UnaryForm make spelling) (child : Renders typedefs expr) :
    Renders typedefs (make expr) := by
  obtain ⟨tokens, grammar, lexed⟩ := child
  refine ⟨.punctuator "(" :: .punctuator spelling :: tokens ++ [.punctuator ")"],
    of_primary (.parenthesized (.widen (by decide +kernel)
      (form.expression (.widen (by decide +kernel) grammar.unary)))), ?_⟩
  intro marker rest safe
  have close := separator_prefix (spelling := ")") (by simp) (marker :: rest)
  have inner := lexed ')' (marker :: rest) (tail_safe_separator expr (by simp))
  have operator : CTokens.Prefix (spelling.toList ++ expr.render.toList ++ ')' :: marker :: rest)
      [.punctuator spelling] (expr.render.toList ++ ')' :: marker :: rest) := by
    apply CTokens.punctuator_prefix
      (Syntax.punctuator_before_expression
        (by cases form <;> decide +kernel) expr grammar.unary.identifier_inputs (')' :: marker :: rest))
    cases form <;> simp [CTokens.PunctuationSafe]
  have openParen := separator_prefix (spelling := "(") (by simp)
    (spelling.toList ++ expr.render.toList ++ ')' :: marker :: rest)
  simpa only [form.printed, String.toList_append, List.append_assoc, List.cons_append, List.nil_append] using
    openParen.append (operator.append (inner.append close))

theorem cast_renders (type : TypeSpelling typedefs name) (child : Renders typedefs expr) :
    Renders typedefs (.cast name expr) := by
  obtain ⟨typeTokens, type⟩ := type
  obtain ⟨tokens, grammar, lexed⟩ := child
  refine ⟨.punctuator "(" :: (.punctuator "(" :: typeTokens ++ [.punctuator ")"] ++ tokens) ++
      [.punctuator ")"],
    of_primary (.parenthesized (.widen (by decide +kernel)
      (.cast type (.widen (by decide +kernel) grammar.unary)))), ?_⟩
  intro marker rest safe
  have close := separator_prefix (spelling := ")") (by simp) (marker :: rest)
  have inner := lexed ')' (marker :: rest) (tail_safe_separator expr (by simp))
  have typeClose := separator_prefix (spelling := ")") (by simp)
    (expr.render.toList ++ ')' :: marker :: rest)
  have typeChars := type.lexical ')' (by simp) (expr.render.toList ++ ')' :: marker :: rest)
  have typeOpen := separator_prefix (spelling := "(") (by simp)
    (name.toList ++ ')' :: (expr.render.toList ++ ')' :: marker :: rest))
  have openParen := separator_prefix (spelling := "(") (by simp)
    ('(' :: (name.toList ++ ')' :: (expr.render.toList ++ ')' :: marker :: rest)))
  simpa only [Expr.render, String.toList_append, List.append_assoc, List.cons_append, List.nil_append] using
    openParen.append (typeOpen.append (typeChars.append (typeClose.append (inner.append close))))

theorem sizeof_renders (type : TypeSpelling typedefs name) : Renders typedefs (.sizeof name) := by
  obtain ⟨tokens, type⟩ := type
  refine ⟨[.word "sizeof", .punctuator "("] ++ tokens ++ [.punctuator ")"],
    ⟨.sizeof type, fun impossible => False.elim impossible⟩, ?_⟩
  intro marker rest safe
  have close := separator_prefix (spelling := ")") (by simp) (marker :: rest)
  have typeChars := type.lexical ')' (by simp) (marker :: rest)
  have openParen := separator_prefix (spelling := "(") (by simp) (name.toList ++ ')' :: marker :: rest)
  have keyword := CTokens.word_prefix (name := "sizeof")
    (show CIdentifierToken.WordParts "sizeof" from ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩)
    (marker := '(') (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (name.toList ++ ')' :: marker :: rest)
  simpa only [Expr.render, String.toList_append, List.append_assoc, List.cons_append, List.nil_append] using
    keyword.append (openParen.append (typeChars.append close))

theorem index_renders (base : Renders typedefs expr) (post : Postfix expr)
    (index : Renders typedefs i) : Renders typedefs (.index expr i) := by
  obtain ⟨baseTokens, baseGrammar, baseLex⟩ := base
  obtain ⟨indexTokens, indexGrammar, indexLex⟩ := index
  refine ⟨baseTokens ++ [.punctuator "["] ++ indexTokens ++ [.punctuator "]"],
    of_postfix (.index (baseGrammar.asPostfix post)
      (.widen (by decide +kernel) indexGrammar.unary)), ?_⟩
  intro marker rest safe
  have close := separator_prefix (spelling := "]") (by simp) (marker :: rest)
  have inner := indexLex ']' (marker :: rest) (tail_safe_separator i (by simp))
  have openBracket := separator_prefix (spelling := "[") (by simp)
    (i.render.toList ++ ']' :: marker :: rest)
  have baseChars := baseLex '[' (i.render.toList ++ ']' :: marker :: rest)
    (tail_safe_separator expr (by simp))
  simpa only [Expr.render, String.toList_append, List.append_assoc, List.cons_append, List.nil_append] using
    baseChars.append (openBracket.append (inner.append close))

private def fieldSymbol (pointer : Bool) : String := if pointer then "->" else "."
private def fieldStart (pointer : Bool) : Char := if pointer then '-' else '.'
private def fieldRest (pointer : Bool) : List Char := if pointer then ['>'] else []

private theorem field_tail_safe (allowed : FieldBase expr) (pointer : Bool) :
    TailSafe expr (fieldStart pointer) := by
  cases expr <;> cases pointer <;> simp only [FieldBase, TailSafe] at allowed ⊢ <;>
    first | contradiction | decide +kernel

theorem field_renders (base : Renders typedefs expr) (post : Postfix expr) (allowed : FieldBase expr)
    (valid : CIdentifier.valid [] name = true) (pointer : Bool) :
    Renders typedefs (.field expr name pointer) := by
  obtain ⟨baseTokens, baseGrammar, baseLex⟩ := base
  have phrase : Expression typedefs .postfix
      (baseTokens ++ [.punctuator (fieldSymbol pointer), .word name]) (.field expr name pointer) := by
    cases pointer with
    | false => exact .field (baseGrammar.asPostfix post) valid
    | true => exact .pointerField (baseGrammar.asPostfix post) valid
  refine ⟨.punctuator "(" :: (baseTokens ++ [.punctuator (fieldSymbol pointer), .word name]) ++
      [.punctuator ")"],
    of_primary (.parenthesized (.widen (by decide +kernel) phrase)), ?_⟩
  intro marker rest safe
  have close := separator_prefix (spelling := ")") (by simp) (marker :: rest)
  have memberName := CTokens.word_prefix (CIdentifier.word_parts [] name valid)
    (marker := ')') (by decide +kernel) (by decide +kernel) (by decide +kernel) (marker :: rest)
  have symbol : CTokens.Prefix
      ((fieldSymbol pointer).toList ++ name.toList ++ ')' :: marker :: rest)
      [.punctuator (fieldSymbol pointer)] (name.toList ++ ')' :: marker :: rest) := by
    apply CTokens.punctuator_prefix
    · simpa only [Expr.render] using Syntax.punctuator_before_expression
        (spelling := fieldSymbol pointer) (by cases pointer <;> decide +kernel)
        (.id name) (typedefs := []) (by simpa only [IdentifierInputs] using valid) (')' :: marker :: rest)
    · obtain ⟨first, tail, chars, start, remaining⟩ := CIdentifier.word_parts [] name valid
      have notDigit := CLexical.identStart_not_digit start
      cases pointer <;> simp [fieldSymbol, CTokens.PunctuationSafe, chars, notDigit]
  have baseChars := baseLex (fieldStart pointer)
    (fieldRest pointer ++ name.toList ++ ')' :: marker :: rest) (field_tail_safe allowed pointer)
  have afterBase := symbol.append (memberName.append close)
  have symbols : (fieldSymbol pointer).toList = fieldStart pointer :: fieldRest pointer := by
    cases pointer <;> rfl
  have remaining : CTokens.Prefix
      (fieldStart pointer :: (fieldRest pointer ++ name.toList ++ ')' :: marker :: rest))
      ([.punctuator (fieldSymbol pointer)] ++ [.word name] ++ [.punctuator ")"]) (marker :: rest) := by
    simpa only [symbols, List.cons_append, List.append_assoc] using afterBase
  have openParen := separator_prefix (spelling := "(") (by simp)
    (expr.render.toList ++ fieldStart pointer :: (fieldRest pointer ++ name.toList ++ ')' :: marker :: rest))
  have printed := openParen.append (baseChars.append remaining)
  cases pointer <;>
    simpa only [Expr.render, String.toList_append, List.append_assoc, List.cons_append, List.nil_append,
      fieldSymbol, fieldStart, fieldRest, Bool.false_eq_true, ↓reduceIte] using printed

def ArgumentsRender (typedefs : List String) (args : List Expr) : Prop :=
  ∃ tokens, ((args = [] ∧ tokens = []) ∨ Arguments typedefs tokens args) ∧
    ∀ rest, CTokens.Prefix
      ((String.intercalate ", " (args.map Expr.render)).toList ++ ')' :: rest) tokens (')' :: rest)

theorem arguments_render (all : ∀ arg ∈ args, Renders typedefs arg) : ArgumentsRender typedefs args := by
  induction args with
  | nil => exact ⟨[], Or.inl ⟨rfl, rfl⟩, fun _ => .done⟩
  | cons first remaining ih =>
      obtain ⟨firstTokens, firstGrammar, firstLex⟩ := all first (by simp)
      cases remaining with
      | nil =>
          refine ⟨firstTokens, Or.inr (.one (.widen (by decide +kernel) firstGrammar.unary)), ?_⟩
          intro rest
          simpa only [List.map_cons, List.map_nil, CText.intercalate_one] using
            firstLex ')' rest (tail_safe_separator first (by simp))
      | cons second remaining =>
          obtain ⟨restTokens, restGrammar, restLex⟩ := ih (fun arg member => all arg (by simp [member]))
          have nonempty : Arguments typedefs restTokens (second :: remaining) := by
            rcases restGrammar with impossible | grammar
            · cases impossible.1
            · exact grammar
          refine ⟨firstTokens ++ [.punctuator ","] ++ restTokens,
            Or.inr (.cons (.widen (by decide +kernel) firstGrammar.unary) nonempty), ?_⟩
          intro rest
          have afterComma : CTokens.Prefix
              (' ' :: ((String.intercalate ", " ((second :: remaining).map Expr.render)).toList ++ ')' :: rest))
              restTokens (')' :: rest) := .space (by decide +kernel) (restLex rest)
          have comma := separator_prefix (spelling := ",") (by simp)
            (' ' :: ((String.intercalate ", " ((second :: remaining).map Expr.render)).toList ++ ')' :: rest))
          have initial := firstLex ','
            (' ' :: ((String.intercalate ", " ((second :: remaining).map Expr.render)).toList ++ ')' :: rest))
            (tail_safe_separator first (by simp))
          simpa only [List.map_cons, CText.intercalate_cons, String.toList_append,
            List.append_assoc, List.cons_append, List.nil_append] using
            initial.append (comma.append afterComma)

theorem call_renders (base : Renders typedefs fn) (post : Postfix fn)
    (all : ∀ arg ∈ args, Renders typedefs arg) : Renders typedefs (.call fn args) := by
  obtain ⟨baseTokens, baseGrammar, baseLex⟩ := base
  obtain ⟨argsTokens, argsGrammar, argsLex⟩ := arguments_render all
  have phrase : Expression typedefs .postfix
      (baseTokens ++ [.punctuator "("] ++ argsTokens ++ [.punctuator ")"]) (.call fn args) := by
    rcases argsGrammar with ⟨rfl, rfl⟩ | nonempty
    · simpa using Expression.callEmpty (baseGrammar.asPostfix post)
    · exact .call (baseGrammar.asPostfix post) nonempty
  refine ⟨_, of_postfix phrase, ?_⟩
  intro marker rest safe
  have close := separator_prefix (spelling := ")") (by simp) (marker :: rest)
  have arguments := argsLex (marker :: rest)
  have openParen := separator_prefix (spelling := "(") (by simp)
    ((String.intercalate ", " (args.map Expr.render)).toList ++ ')' :: marker :: rest)
  have baseChars := baseLex '('
    ((String.intercalate ", " (args.map Expr.render)).toList ++ ')' :: marker :: rest)
    (tail_safe_separator fn (by simp))
  simpa only [Expr.render, String.toList_append, List.append_assoc, List.cons_append, List.nil_append] using
    baseChars.append (openParen.append (arguments.append close))

/-- Domain of the unchanged printer. In addition to lexical names and type
spellings, postfix positions exclude an unparenthesized sizeof expression.
Bare numeric field bases would fuse with '.'/'-'; such field expressions are
also C-type-invalid. No field/call/index is licensed by syntax alone for execution. -/
inductive Printable (typedefs : List String) : Expr → Prop where
  | identifier : CIdentifier.valid typedefs name = true → Printable typedefs (.id name)
  | natural : Printable typedefs (.nat n)
  | string : Printable typedefs (.str value)
  | binary : Printable typedefs a → Printable typedefs b → Printable typedefs (.bin op a b)
  | not : Printable typedefs expr → Printable typedefs (.not expr)
  | dereference : Printable typedefs expr → Printable typedefs (.deref expr)
  | address : Printable typedefs expr → Printable typedefs (.address expr)
  | field : Printable typedefs expr → Postfix expr → FieldBase expr →
      CIdentifier.valid [] name = true → Printable typedefs (.field expr name pointer)
  | index : Printable typedefs expr → Postfix expr → Printable typedefs i →
      Printable typedefs (.index expr i)
  | call : Printable typedefs fn → Postfix fn → (∀ arg ∈ args, Printable typedefs arg) →
      Printable typedefs (.call fn args)
  | cast : TypeSpelling typedefs name → Printable typedefs expr → Printable typedefs (.cast name expr)
  | sizeof : TypeSpelling typedefs name → Printable typedefs (.sizeof name)

/-- Every admissible construction tree prints the intended expression in the
independent C token/precedence grammar, for every safe actual continuation. -/
theorem expression_renders (valid : Printable typedefs expr) : Renders typedefs expr := by
  induction valid with
  | identifier name => exact identifier_renders name
  | natural => exact natural_renders _
  | string => exact string_renders _
  | binary left right hl hr => exact binary_renders _ hl hr
  | not child ih => exact unary_renders .not ih
  | dereference child ih => exact unary_renders .dereference ih
  | address child ih => exact unary_renders .address ih
  | field child post allowed valid ih => exact field_renders ih post allowed valid _
  | index child post index hc hi => exact index_renders hc post hi
  | call fn post args hf ha => exact call_renders hf post ha
  | cast type child ih => exact cast_renders type ih
  | sizeof type => exact sizeof_renders type

end Rumoca.CTree.Printer
