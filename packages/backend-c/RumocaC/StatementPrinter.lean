import RumocaC.ExpressionPrinter
import RumocaC.StatementSyntax

/-! Structural certification of the unchanged CTree statement renderer.
The token witness has an independent block-item derivation, and every lexical
step keeps the actual continuation. Indentation and nested block lists are
quantified, rather than checked for a fixed generated example. -/
namespace Rumoca.CTree.Printer
open Syntax
open CTokens (separator_prefix)

def ItemRenders (typedefs : List String) (stmt : Stmt) : Prop :=
  ∃ tokens, BlockItem typedefs tokens stmt ∧ ∀ depth rest,
    CTokens.Prefix ((stmt.render depth).toList ++ rest) tokens rest

def ItemsRender (typedefs : List String) (stmts : List Stmt) : Prop :=
  ∃ tokens, BlockItems typedefs tokens stmts ∧ ∀ depth rest,
    CTokens.Prefix ((String.join (stmts.map fun stmt => stmt.render depth)).toList ++ rest) tokens rest

private theorem terminate_prefix (rest : List Char) :
    CTokens.Prefix (';' :: '\n' :: rest) [.punctuator ";"] rest :=
  (separator_prefix (spelling := ";") (by simp) ('\n' :: rest)).append
    (.space (by decide +kernel) .done)

private theorem equals_prefix (rest : List Char) :
    CTokens.Prefix (' ' :: '=' :: ' ' :: rest) [.punctuator "="] rest := by
  have eq : CTokens.Prefix ('=' :: ' ' :: rest) [.punctuator "="] (' ' :: rest) :=
    CTokens.punctuator_prefix
      (CPunctuator.consumes_space (spelling := "=") (by decide +kernel) rest)
      (by simp [CTokens.PunctuationSafe])
  exact .space (by decide +kernel) (eq.append (.space (by decide +kernel) .done))

private theorem keyword_prefix (member : name ∈ ["return", "if", "else", "while"])
    (delimiter : marker ∈ [' ', ';']) (rest : List Char) :
    CTokens.Prefix (name.toList ++ marker :: rest) [.word name] (marker :: rest) := by
  have parts : CIdentifierToken.WordParts name := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      exact ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at delimiter
  rcases delimiter with rfl | rfl <;>
    exact CTokens.word_prefix parts (by decide +kernel) (by decide +kernel) (by decide +kernel) rest

theorem declare_renders (type : TypeSpelling typedefs name)
    (valid : CIdentifier.valid typedefs variableName = true)
    (value : Renders typedefs expr) : ItemRenders typedefs (.declare name variableName expr) := by
  obtain ⟨typeTokens, type⟩ := type
  obtain ⟨tokens, grammar, lexed⟩ := value
  refine ⟨_, .declare type valid (.widen (by decide +kernel) grammar.unary), ?_⟩
  intro depth rest
  have ending := terminate_prefix rest
  have valueChars := lexed ';' ('\n' :: rest) (tail_safe_separator expr (by simp))
  have eq := equals_prefix (expr.render.toList ++ ';' :: '\n' :: rest)
  have nameChars := CTokens.word_prefix (CIdentifier.word_parts typedefs variableName valid)
    (marker := ' ') (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ('=' :: ' ' :: (expr.render.toList ++ ';' :: '\n' :: rest))
  have typeChars := type.lexical ' ' (by simp)
    (variableName.toList ++ ' ' :: '=' :: ' ' :: (expr.render.toList ++ ';' :: '\n' :: rest))
  have printed := typeChars.append
    (.space (by decide +kernel) (nameChars.append (eq.append (valueChars.append ending))))
  simpa only [Stmt.render, String.toList_append, String.toList_ofList,
    List.append_assoc, List.cons_append, List.nil_append] using printed.indent (2 * depth)

theorem assign_renders (target : Renders typedefs lhs) (value : Renders typedefs rhs) :
    ItemRenders typedefs (.assign lhs rhs) := by
  obtain ⟨leftTokens, leftGrammar, leftLex⟩ := target
  obtain ⟨rightTokens, rightGrammar, rightLex⟩ := value
  refine ⟨_, .assign leftGrammar.unary (.widen (by decide +kernel) rightGrammar.unary), ?_⟩
  intro depth rest
  have ending := terminate_prefix rest
  have rhsChars := rightLex ';' ('\n' :: rest) (tail_safe_separator rhs (by simp))
  have eq := equals_prefix (rhs.render.toList ++ ';' :: '\n' :: rest)
  have lhsChars := leftLex ' ' ('=' :: ' ' :: (rhs.render.toList ++ ';' :: '\n' :: rest))
    (tail_safe_separator lhs (by simp))
  simpa only [Stmt.render, String.toList_append, String.toList_ofList,
    List.append_assoc, List.cons_append, List.nil_append] using
    (lhsChars.append (eq.append (rhsChars.append ending))).indent (2 * depth)

theorem eval_renders (value : Renders typedefs expr) : ItemRenders typedefs (.eval expr) := by
  obtain ⟨tokens, grammar, lexed⟩ := value
  refine ⟨_, .eval (.widen (by decide +kernel) grammar.unary), ?_⟩
  intro depth rest
  have chars := lexed ';' ('\n' :: rest) (tail_safe_separator expr (by simp))
  simpa only [Stmt.render, String.toList_append, String.toList_ofList,
    List.append_assoc, List.cons_append, List.nil_append] using
    (chars.append (terminate_prefix rest)).indent (2 * depth)

theorem return_void_renders : ItemRenders typedefs (.ret none) := by
  refine ⟨_, .returnVoid, ?_⟩
  intro depth rest
  have word := keyword_prefix (name := "return") (by simp) (marker := ';') (by simp) ('\n' :: rest)
  simpa only [Stmt.render, String.toList_append, String.toList_ofList,
    List.append_assoc, List.cons_append, List.nil_append] using
    (word.append (terminate_prefix rest)).indent (2 * depth)

theorem return_value_renders (value : Renders typedefs expr) : ItemRenders typedefs (.ret (some expr)) := by
  obtain ⟨tokens, grammar, lexed⟩ := value
  refine ⟨_, .returnValue (.widen (by decide +kernel) grammar.unary), ?_⟩
  intro depth rest
  have chars := lexed ';' ('\n' :: rest) (tail_safe_separator expr (by simp))
  have word := keyword_prefix (name := "return") (by simp) (marker := ' ') (by simp)
    (expr.render.toList ++ ';' :: '\n' :: rest)
  simpa only [Stmt.render, String.toList_append, String.toList_ofList,
    List.append_assoc, List.cons_append, List.nil_append] using
    (word.append (.space (by decide +kernel) (chars.append (terminate_prefix rest)))).indent (2 * depth)

theorem items_render (all : ∀ stmt ∈ stmts, ItemRenders typedefs stmt) :
    ItemsRender typedefs stmts := by
  induction stmts with
  | nil => exact ⟨[], .nil, fun _ _ => .done⟩
  | cons stmt stmts ih =>
      obtain ⟨firstTokens, firstGrammar, firstLex⟩ := all stmt (by simp)
      obtain ⟨restTokens, restGrammar, restLex⟩ := ih (fun stmt member => all stmt (by simp [member]))
      refine ⟨firstTokens ++ restTokens, .cons firstGrammar restGrammar, ?_⟩
      intro depth rest
      have first := firstLex depth
        ((String.join (stmts.map fun stmt => stmt.render depth)).toList ++ rest)
      simpa only [List.map_cons, CString.join_toList, List.flatMap_cons, List.append_assoc] using
        first.append (restLex depth rest)

private theorem compound_prefix {body : List Stmt}
    (lexed : ∀ depth rest, CTokens.Prefix
      ((String.join (body.map fun stmt => stmt.render depth)).toList ++ rest) tokens rest)
    (depth : Nat) (rest : List Char) :
    CTokens.Prefix ((" {\n" ++ String.join (body.map fun stmt => stmt.render (depth + 1)) ++
      String.ofList (List.replicate (2 * depth) ' ') ++ "}").toList ++ rest)
      (.punctuator "{" :: tokens ++ [.punctuator "}"]) rest := by
  have close := (separator_prefix (spelling := "}") (by simp) rest).indent (2 * depth)
  have bodyChars := lexed (depth + 1) (List.replicate (2 * depth) ' ' ++ '}' :: rest)
  have openBrace := separator_prefix (spelling := "{") (by simp)
    ('\n' :: ((String.join (body.map fun stmt => stmt.render (depth + 1))).toList ++
      (List.replicate (2 * depth) ' ' ++ '}' :: rest)))
  have chars := CTokens.Prefix.space (c := ' ') (by decide +kernel)
    (openBrace.append (.space (by decide +kernel) (bodyChars.append close)))
  simpa only [String.toList_append, String.toList_ofList, List.append_assoc,
    List.cons_append, List.nil_append] using chars

private theorem control_prefix {stmts : List Stmt} (member : keyword ∈ ["if", "while"])
    (condition : ∀ marker rest, TailSafe expr marker →
      CTokens.Prefix (expr.render.toList ++ marker :: rest) conditionTokens (marker :: rest))
    (body : ∀ depth rest, CTokens.Prefix
      ((String.join (stmts.map fun stmt => stmt.render depth)).toList ++ rest) bodyTokens rest)
    (depth : Nat) (rest : List Char) :
    CTokens.Prefix ((keyword ++ " (" ++ expr.render ++ ") {\n" ++
      String.join (stmts.map fun stmt => stmt.render (depth + 1)) ++
      String.ofList (List.replicate (2 * depth) ' ') ++ "}").toList ++ rest)
      ([.word keyword, .punctuator "("] ++ conditionTokens ++
        [.punctuator ")", .punctuator "{"] ++ bodyTokens ++ [.punctuator "}"]) rest := by
  let suffix := (" {\n" ++ String.join (stmts.map fun stmt => stmt.render (depth + 1)) ++
    String.ofList (List.replicate (2 * depth) ' ') ++ "}").toList ++ rest
  have compound := compound_prefix body depth rest
  have close := separator_prefix (spelling := ")") (by simp) suffix
  have conditionChars := condition ')' suffix (tail_safe_separator expr (by simp))
  have openParen := separator_prefix (spelling := "(") (by simp) (expr.render.toList ++ ')' :: suffix)
  have keywordMember : keyword ∈ ["return", "if", "else", "while"] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    rcases member with rfl | rfl <;> simp
  have word := keyword_prefix keywordMember (marker := ' ') (by simp)
    ('(' :: (expr.render.toList ++ ')' :: suffix))
  simpa only [suffix, String.toList_append, String.toList_ofList, List.append_assoc,
    List.cons_append, List.nil_append] using
    word.append (.space (by decide +kernel)
      (openParen.append (conditionChars.append (close.append compound))))

theorem while_renders (condition : Renders typedefs expr) (body : ItemsRender typedefs stmts) :
    ItemRenders typedefs (.whileLoop expr stmts) := by
  obtain ⟨conditionTokens, conditionGrammar, conditionLex⟩ := condition
  obtain ⟨bodyTokens, bodyGrammar, bodyLex⟩ := body
  refine ⟨_, .whileLoop (.widen (by decide +kernel) conditionGrammar.unary) bodyGrammar, ?_⟩
  intro depth rest
  have chars := control_prefix (keyword := "while") (by simp) conditionLex bodyLex depth ('\n' :: rest)
  simpa only [Stmt.render, String.toList_append, String.toList_ofList, List.append_assoc,
    List.cons_append, List.nil_append] using
    (chars.append (.space (by decide +kernel) .done)).indent (2 * depth)

theorem if_then_renders (condition : Renders typedefs expr) (body : ItemsRender typedefs stmts) :
    ItemRenders typedefs (.branch expr stmts []) := by
  obtain ⟨conditionTokens, conditionGrammar, conditionLex⟩ := condition
  obtain ⟨bodyTokens, bodyGrammar, bodyLex⟩ := body
  refine ⟨_, .ifThen (.widen (by decide +kernel) conditionGrammar.unary) bodyGrammar, ?_⟩
  intro depth rest
  have chars := control_prefix (keyword := "if") (by simp) conditionLex bodyLex depth ('\n' :: rest)
  simpa only [Stmt.render, List.isEmpty_nil, ↓reduceIte, String.toList_append,
    String.toList_ofList, List.append_assoc, List.cons_append, List.nil_append] using
    (chars.append (.space (by decide +kernel) .done)).indent (2 * depth)

theorem if_else_renders (condition : Renders typedefs expr) (yes : ItemsRender typedefs yesBody)
    (no : ItemsRender typedefs noBody) (nonempty : noBody.isEmpty = false) :
    ItemRenders typedefs (.branch expr yesBody noBody) := by
  obtain ⟨conditionTokens, conditionGrammar, conditionLex⟩ := condition
  obtain ⟨yesTokens, yesGrammar, yesLex⟩ := yes
  obtain ⟨noTokens, noGrammar, noLex⟩ := no
  refine ⟨_, .ifElse (.widen (by decide +kernel) conditionGrammar.unary) yesGrammar noGrammar, ?_⟩
  intro depth rest
  let tailText := " {\n" ++ String.join (noBody.map fun stmt => stmt.render (depth + 1)) ++
    String.ofList (List.replicate (2 * depth) ' ') ++ "}"
  have compound := compound_prefix noLex depth ('\n' :: rest)
  have opening : " {\n".toList = [' ', '{', '\n'] := rfl
  have tailChars : tailText.toList = ' ' :: tailText.toList.tail := by
    simp only [tailText, String.toList_append, opening, List.append_assoc, List.cons_append, List.nil_append,
      List.tail_cons]
  have word := keyword_prefix (name := "else") (by simp) (marker := ' ') (by simp)
    (tailText.toList.tail ++ '\n' :: rest)
  have afterWord : CTokens.Prefix (' ' :: (tailText.toList.tail ++ '\n' :: rest))
      (.punctuator "{" :: noTokens ++ [.punctuator "}"]) ('\n' :: rest) := by
    change CTokens.Prefix _ _ ('\n' :: rest) at compound
    simpa only [← List.cons_append, ← tailChars] using compound
  have elseChars := CTokens.Prefix.space (c := ' ') (by decide +kernel)
    (word.append (afterWord.append (.space (by decide +kernel) .done)))
  have first := control_prefix (keyword := "if") (by simp) conditionLex yesLex depth
    (' ' :: ("else".toList ++ ' ' :: (tailText.toList.tail ++ '\n' :: rest)))
  have chars := (first.append elseChars).indent (2 * depth)
  simpa only [Stmt.render, nonempty, Bool.false_eq_true, ↓reduceIte, tailText,
    String.toList_append, opening, String.toList_ofList, List.append_assoc, List.cons_append, List.nil_append,
    List.tail_cons] using chars

inductive ItemPrintable (typedefs : List String) : Stmt → Prop where
  | declare : TypeSpelling typedefs type → CIdentifier.valid typedefs name = true →
      Printable typedefs value → ItemPrintable typedefs (.declare type name value)
  | assign : Printable typedefs target → Printable typedefs value →
      ItemPrintable typedefs (.assign target value)
  | eval : Printable typedefs value → ItemPrintable typedefs (.eval value)
  | returnVoid : ItemPrintable typedefs (.ret none)
  | returnValue : Printable typedefs value → ItemPrintable typedefs (.ret (some value))
  | branch : Printable typedefs condition → (∀ stmt ∈ yes, ItemPrintable typedefs stmt) →
      (∀ stmt ∈ no, ItemPrintable typedefs stmt) → ItemPrintable typedefs (.branch condition yes no)
  | whileLoop : Printable typedefs condition → (∀ stmt ∈ body, ItemPrintable typedefs stmt) →
      ItemPrintable typedefs (.whileLoop condition body)

/-- Every admitted block item prints its intended token grammar, at every
indentation depth and with every actual continuation. -/
theorem statement_renders (valid : ItemPrintable typedefs stmt) : ItemRenders typedefs stmt := by
  induction valid with
  | declare type name value => exact declare_renders type name (expression_renders value)
  | assign target value => exact assign_renders (expression_renders target) (expression_renders value)
  | eval value => exact eval_renders (expression_renders value)
  | returnVoid => exact return_void_renders
  | returnValue value => exact return_value_renders (expression_renders value)
  | @branch condition yes no expr hy hn iy ino =>
      cases no with
      | nil => exact if_then_renders (expression_renders expr) (items_render iy)
      | cons first rest =>
          exact if_else_renders (expression_renders expr) (items_render iy) (items_render ino) rfl
  | whileLoop expr body ih => exact while_renders (expression_renders expr) (items_render ih)

end Rumoca.CTree.Printer
