import RumocaEFMI.CSyntax
import XML.Proofs

open _root_.Parser

/-! Structural correctness of the Production C printer. The conclusion uses
the independent token grammar and maximal-munch character relation in
`CSyntax`; none of these proofs invokes the candidate C reader. -/
namespace Rumoca.EFMI.CSyntax
open CTree

private theorem word_parts (name : String) (h : identifier name = true) :
    ∃ c cs, name.toList = c :: cs ∧ identStart c = true ∧ cs.all identRest = true :=
  CIdentifier.word_parts _ name h

private theorem lex_word (name : String) (c : Char) (rest : List Char) (ts : List Token)
    (valid : ∃ head tail, name.toList = head :: tail ∧
      identStart head = true ∧ tail.all identRest = true)
    (stop : identRest c = false) (h : Scanner.Lexes config (c :: rest) ts) :
    Scanner.Lexes config (name.toList ++ c :: rest) (.literal name :: ts) :=
  CIdentifier.lex_word config rfl rfl rfl rfl name c rest ts valid stop h

/-- Discharge fixed punctuation/keyword fragments by the lexical constructors.
Only short character-class facts are reduced; the C parser is not evaluated. -/
macro "efmi_lex_fixed" : tactic => `(tactic|
  repeat first
  | assumption
  | exact Scanner.Lexes.nil
  | apply Scanner.Lexes.space (by decide +kernel)
  | apply Scanner.Lexes.word (by decide +kernel) (by decide +kernel)
  | apply Scanner.Lexes.number (by decide +kernel) (by decide +kernel) (by decide +kernel)
  | apply Scanner.Lexes.symbol (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (Scanner.SymbolLexes.single (by decide +kernel) (by decide +kernel))
  | apply Scanner.Lexes.symbol (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (Scanner.SymbolLexes.pair (by decide +kernel)))

theorem atom_render (atom : Atom) (valid : atom.valid = true)
    (c : Char) (rest : List Char) (ts : List Token)
    (stop : identRest c = false) (h : Scanner.Lexes config (c :: rest) ts) :
    Scanner.Lexes config (atom.tree.render.toList ++ c :: rest)
      (atom.tokens.map Token.literal ++ ts) := by
  cases atom with
  | «variable» name =>
    simpa only [Atom.tree, Expr.render, Atom.tokens, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append] using
      lex_word name c rest ts (word_parts name valid) stop h
  | member base field =>
    simp only [Atom.valid, Bool.and_eq_true] at valid
    simp only [Atom.tree, Expr.render, ↓reduceIte, String.toList_append,
      Atom.tokens, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.append_assoc]
    efmi_lex_fixed
    apply lex_word base '-' _ _ (word_parts base valid.1) (by decide +kernel)
    efmi_lex_fixed
    apply lex_word field ')' _ _ (word_parts field valid.2) (by decide +kernel)
    efmi_lex_fixed
  | zero | one =>
    simp only [Atom.tree, Expr.render, Atom.tokens, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append]
    efmi_lex_fixed

theorem term_render (term : Term) (valid : term.valid = true)
    (c : Char) (rest : List Char) (ts : List Token)
    (stop : identRest c = false) (h : Scanner.Lexes config (c :: rest) ts) :
    Scanner.Lexes config (term.tree.render.toList ++ c :: rest)
      (term.tokens.map Token.literal ++ ts) := by
  cases term with
  | atom a => exact atom_render a valid c rest ts stop h
  | add a b =>
    simp only [Term.valid, Bool.and_eq_true] at valid
    simp only [Term.tree, Expr.render, BinOp.render, String.toList_append, Term.tokens,
      List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.append_assoc]
    efmi_lex_fixed
    apply atom_render a valid.1 ' ' _ _ (by decide +kernel)
    efmi_lex_fixed
    apply atom_render b valid.2 ')' _ _ (by decide +kernel)
    efmi_lex_fixed

private theorem lex_indent (n : Nat) (rest : List Char) (ts : List Token)
    (h : Scanner.Lexes config rest ts) :
    Scanner.Lexes config (List.replicate n ' ' ++ rest) ts := by
  induction n with
  | zero => exact h
  | succ n ih => exact Scanner.Lexes.space (by decide +kernel) ih

theorem statement_render (stmt : Statement) (valid : stmt.valid = true)
    (depth : Nat) (rest : List Char) (ts : List Token)
    (h : Scanner.Lexes config rest ts) :
    Scanner.Lexes config ((stmt.tree.render depth).toList ++ rest)
      (stmt.tokens.map Token.literal ++ ts) := by
  cases stmt with
  | declare name value =>
    simp only [Statement.valid, Bool.and_eq_true] at valid
    simp only [Statement.tree, Stmt.render, String.toList_append, String.toList_ofList,
      Statement.tokens, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_assoc]
    apply lex_indent
    efmi_lex_fixed
    apply lex_word name ' ' _ _ (word_parts name valid.1) (by decide +kernel)
    efmi_lex_fixed
    apply term_render value valid.2 ';' _ _ (by decide +kernel)
    efmi_lex_fixed
  | assign target value =>
    have hv : target.valid = true ∧ value.valid = true := by
      cases target <;> simp_all [Statement.valid, Atom.valid, Bool.and_eq_true, and_assoc]
    simp only [Statement.tree, Stmt.render, String.toList_append, String.toList_ofList,
      Statement.tokens, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_assoc]
    apply lex_indent
    apply atom_render target hv.1 ' ' _ _ (by decide +kernel)
    efmi_lex_fixed
    apply term_render value hv.2 ';' _ _ (by decide +kernel)
    efmi_lex_fixed

theorem statements_render (stmts : List Statement) (valid : stmts.all Statement.valid = true)
    (depth : Nat) (rest : List Char) (ts : List Token)
    (h : Scanner.Lexes config rest ts) :
    Scanner.Lexes config
      (stmts.flatMap (fun stmt => (stmt.tree.render depth).toList) ++ rest)
      ((stmts.flatMap Statement.tokens).map Token.literal ++ ts) := by
  induction stmts with
  | nil => exact h
  | cons stmt stmts ih =>
    simp only [List.all_cons, Bool.and_eq_true] at valid
    simp only [List.flatMap_cons, List.map_append, List.append_assoc]
    exact statement_render stmt valid.1 depth _ _ (ih valid.2)

private theorem intercalate_one (separator value : String) :
    String.intercalate separator [value] = value := rfl

theorem function_render (f : Function) (valid : f.valid = true)
    (rest : List Char) (ts : List Token) (h : Scanner.Lexes config rest ts) :
    Scanner.Lexes config (f.tree.render.toList ++ rest) (f.tokens.map Token.literal ++ ts) := by
  simp only [Function.valid, Bool.and_eq_true] at valid
  simp only [Function.tree, CTree.Function.render, Signature.render, Parameter.render,
    List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil,
    intercalate_one, String.toList_append, String.append_empty, Function.tokens,
    List.map_append, List.map_map, XML.join_toList, List.flatMap_append, List.flatMap_map,
    List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append, List.append_nil,
    List.append_assoc, Stmt.render, Expr.render, String.toList_ofList]
  efmi_lex_fixed
  apply lex_word f.name '(' _ _ (word_parts _ valid.1.1) (by decide +kernel)
  efmi_lex_fixed
  apply lex_word f.parameter ')' _ _ (word_parts _ valid.1.2) (by decide +kernel)
  efmi_lex_fixed
  apply statements_render f.statements valid.2 1
  efmi_lex_fixed

/-- Every syntactically valid program in the existing Production C profile
prints into that same independent text grammar with the identical target tree.
This is structural in all names, expressions and statement lists, rather than
a computation on the unit integrator or an assumption about a C reader. -/
theorem program_render (program : Program) (valid : program.valid = true) :
    Denotes program.tree.render program := by
  refine ⟨valid, (program.startup.tree.render ++ program.recalibrate.tree.render ++
    program.doStep.tree.render).toList, ?_, ?_⟩
  · simp only [Program.tree, Production.Module.render, String.toList_append, List.append_assoc]
  · simp only [Program.valid, Bool.and_eq_true] at valid
    simp only [String.toList_append, Program.tokens, List.map_append, List.append_assoc]
    exact function_render program.startup valid.1.1 _ _
      (function_render program.recalibrate valid.1.2 _ _
        (by simpa using function_render program.doStep valid.2 [] [] Scanner.Lexes.nil))

end Rumoca.EFMI.CSyntax
