import RumocaC.TensorProgramSyntax

/-! Structural printer certificate for complete prepared tensor-call functions.
The grammar checks target identifiers, parameter scope and pointer mutability;
the proof is independent of the number of instructions and tensor extents. -/
namespace Rumoca.CTensor.Lowering.Syntax
open CTree _root_.Parser

private theorem lex_word (name : String) (valid : identifier name = true)
    (c : Char) (rest : List Char) (ts : List Token)
    (stop : identRest c = false) (h : Scanner.Lexes CTensor.Syntax.config (c :: rest) ts) :
    Scanner.Lexes CTensor.Syntax.config (name.toList ++ c :: rest) (.literal name :: ts) :=
  CIdentifier.lex_word _ rfl rfl rfl rfl name c rest ts
    (CIdentifier.word_parts _ name valid) stop h

private theorem lex_indent (n : Nat) (rest : List Char) (ts : List Token)
    (h : Scanner.Lexes CTensor.Syntax.config rest ts) :
    Scanner.Lexes CTensor.Syntax.config (List.replicate n ' ' ++ rest) ts := by
  induction n with
  | zero => exact h
  | succ n ih => exact Scanner.Lexes.space (by decide +kernel) ih

private theorem intercalate_one (separator value : String) :
    String.intercalate separator [value] = value := rfl
private theorem intercalate_cons (separator first second : String) (rest : List String) :
    String.intercalate separator (first :: second :: rest) =
      first ++ separator ++ String.intercalate separator (second :: rest) := by
  have go : ∀ rest : List String, ∀ lead acc : String,
      String.intercalate separator ((lead ++ acc) :: rest) =
        lead ++ String.intercalate separator (acc :: rest) := by
    intro rest
    induction rest with
    | nil => intros; rfl
    | cons s ss ih =>
      intro lead acc
      change String.intercalate separator (((lead ++ acc) ++ separator ++ s) :: ss) =
        lead ++ String.intercalate separator ((acc ++ separator ++ s) :: ss)
      simpa only [String.append_assoc] using ih lead (acc ++ separator ++ s)
  exact go rest (first ++ separator) second

private theorem list_intercalate_one (sep value : List α) : List.intercalate sep [value] = value := by
  simp [List.intercalate]

private theorem list_intercalate_cons (sep first second : List α) (rest : List (List α)) :
    List.intercalate sep (first :: second :: rest) =
      first ++ sep ++ List.intercalate sep (second :: rest) := by
  simp only [List.intercalate, List.intersperse_cons₂, List.flatten_cons, List.append_assoc]

theorem diagonal_statement_render (coeff output count cells : String)
    (valid : [coeff, output, count, cells].all identifier = true)
    (depth : Nat) (rest : List Char) (ts : List Token)
    (h : Scanner.Lexes CTensor.Syntax.config rest ts) :
    Scanner.Lexes CTensor.Syntax.config
      (((Stmt.eval (.call (.id "rumoca_tensor_diagonal") [.id coeff, .id output, .id count, .id cells])).render depth).toList ++ rest)
      ((["rumoca_tensor_diagonal", "(", coeff, ",", output, ",", count, ",", cells, ")", ";"].map Token.literal) ++ ts) := by
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at valid
  simp only [Stmt.render, Expr.render, List.map_cons, List.map_nil, intercalate_cons, intercalate_one,
    String.toList_append, String.toList_ofList, List.cons_append, List.nil_append, List.append_assoc]
  apply lex_indent
  c_lex_fixed
  apply lex_word coeff valid.1 ',' _ _ (by decide +kernel)
  c_lex_fixed
  apply lex_word output valid.2.1 ',' _ _ (by decide +kernel)
  c_lex_fixed
  apply lex_word count valid.2.2.1 ',' _ _ (by decide +kernel)
  c_lex_fixed
  apply lex_word cells valid.2.2.2 ')' _ _ (by decide +kernel)
  c_lex_fixed

theorem statement_render (s : Statement) (valid : s.names.all identifier = true)
    (depth : Nat) (rest : List Char) (ts : List Token)
    (h : Scanner.Lexes CTensor.Syntax.config rest ts) :
    Scanner.Lexes CTensor.Syntax.config ((s.tree.render depth).toList ++ rest)
      (s.tokens.map Token.literal ++ ts) := by
  cases s with
  | fill value output count =>
    simp only [Statement.names, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at valid
    cases value <;>
      simp only [Statement.tree, Stmt.render, Expr.render, List.map_cons, List.map_nil,
        intercalate_cons, intercalate_one, String.toList_append, String.toList_ofList,
        Statement.tokens, List.cons_append, List.nil_append, List.append_assoc] <;>
      apply lex_indent <;> c_lex_fixed <;>
      apply lex_word output valid.1 ',' _ _ (by decide +kernel) <;> c_lex_fixed <;>
      apply lex_word count valid.2 ')' _ _ (by decide +kernel) <;> c_lex_fixed
  | binary op left right output count =>
    simp only [Statement.names, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at valid
    cases op <;>
      simp only [Statement.tree, binaryName, Stmt.render, Expr.render, List.map_cons, List.map_nil,
        intercalate_cons, intercalate_one, String.toList_append, String.toList_ofList,
        Statement.tokens, List.cons_append, List.nil_append, List.append_assoc] <;>
      apply lex_indent <;> c_lex_fixed <;>
      apply lex_word left valid.1 ',' _ _ (by decide +kernel) <;> c_lex_fixed <;>
      apply lex_word right valid.2.1 ',' _ _ (by decide +kernel) <;> c_lex_fixed <;>
      apply lex_word output valid.2.2.1 ',' _ _ (by decide +kernel) <;> c_lex_fixed <;>
      apply lex_word count valid.2.2.2 ')' _ _ (by decide +kernel) <;> c_lex_fixed
  | diagonal coefficients output count cells =>
    exact diagonal_statement_render coefficients output count cells valid depth rest ts h

theorem parameter_render (p : Parameter) (valid : identifier p.name = true)
    (c : Char) (rest : List Char) (ts : List Token) (stop : identRest c = false)
    (h : Scanner.Lexes CTensor.Syntax.config (c :: rest) ts) :
    Scanner.Lexes CTensor.Syntax.config (p.tree.render.toList ++ c :: rest)
      (p.tokens.map Token.literal ++ ts) := by
  rcases p with ⟨kind, name⟩
  cases kind <;>
    simp only [Parameter.tree, ParamKind.type, CTree.Parameter.render,
      String.toList_append, Parameter.tokens, ParamKind.tokens,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.append_assoc] <;> c_lex_fixed <;>
    exact lex_word name valid c rest ts stop h

theorem parameters_render (params : List Parameter)
    (valid : params.all (fun p => identifier p.name) = true) (nonempty : params ≠ [])
    (rest : List Char) (ts : List Token)
    (h : Scanner.Lexes CTensor.Syntax.config (')' :: rest) ts) :
    Scanner.Lexes CTensor.Syntax.config
      ((String.intercalate ", " (params.map (fun p => p.tree.render))).toList ++ ')' :: rest)
      ((List.intercalate [","] (params.map Parameter.tokens)).map Token.literal ++ ts) := by
  induction params with
  | nil => contradiction
  | cons p params ih =>
    simp only [List.all_cons, Bool.and_eq_true] at valid
    cases params with
    | nil =>
      simpa only [List.map_cons, List.map_nil, intercalate_one, list_intercalate_one] using
        parameter_render p valid.1 ')' rest ts (by decide +kernel) h
    | cons next params =>
      simp only [List.map_cons, intercalate_cons, String.toList_append, List.append_assoc,
        list_intercalate_cons, List.map_append, List.map_cons,
        List.cons_append, List.nil_append]
      apply parameter_render p valid.1 ',' _ _ (by decide +kernel)
      c_lex_fixed
      exact ih valid.2 (by simp)

theorem statements_render (stmts : List Statement)
    (valid : stmts.all (fun s => s.names.all identifier) = true)
    (rest : List Char) (ts : List Token) (h : Scanner.Lexes CTensor.Syntax.config rest ts) :
    Scanner.Lexes CTensor.Syntax.config
      (stmts.flatMap (fun s => (s.tree.render 1).toList) ++ rest)
      ((stmts.flatMap Statement.tokens).map Token.literal ++ ts) := by
  induction stmts with
  | nil => exact h
  | cons s stmts ih =>
    simp only [List.all_cons, Bool.and_eq_true] at valid
    simp only [List.flatMap_cons, List.map_append, List.append_assoc]
    exact statement_render s valid.1 1 _ _ (ih valid.2)

private theorem join_toList (strings : List String) :
    (String.join strings).toList = strings.flatMap String.toList := by
  have go : ∀ strings : List String, ∀ start : String,
      (strings.foldl (· ++ ·) start).toList = start.toList ++ strings.flatMap String.toList := by
    intro strings
    induction strings with
    | nil => intro start; simp
    | cons s ss ih => intro start; simp [List.foldl, ih, String.toList_append, List.append_assoc]
  simpa [String.join] using go strings ""

theorem render_denotes (f : Function) (valid : f.valid = true) : Denotes f.tree.render f := by
  refine ⟨valid, ?_⟩
  have names : f.statements.all (fun s => s.names.all identifier) = true := by
    have h := valid
    simp only [Function.valid, Bool.and_eq_true] at h
    apply List.all_eq_true.mpr
    intro s hs
    have hv := List.all_eq_true.mp h.2 s hs
    simp only [Statement.valid, Bool.and_eq_true] at hv
    exact hv.1
  simp only [Function.valid, Bool.and_eq_true] at valid
  simp only [Function.tree, CTree.Function.render, Signature.render,
    Function.tokens, String.toList_append, List.map_append,
    List.map_cons, List.map_nil, List.map_map, join_toList, List.flatMap_append,
    List.flatMap_map, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, List.append_nil, List.append_assoc, Stmt.render, String.toList_ofList]
  c_lex_fixed
  apply lex_word f.name valid.1.1.1.1.1 '(' _ _ (by decide +kernel)
  c_lex_fixed
  cases hp : f.parameters with
  | nil =>
    simp only [List.map_nil, List.isEmpty_nil, ↓reduceIte, parameterTokens,
      List.map_cons, List.cons_append, List.nil_append]
    c_lex_fixed
    apply statements_render f.statements names
    c_lex_fixed
  | cons p params =>
    simp only [List.map_cons, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, parameterTokens]
    apply parameters_render (p :: params) (hp ▸ valid.1.1.1.1.2) (by simp)
    c_lex_fixed
    apply statements_render f.statements names
    c_lex_fixed

end Rumoca.CTensor.Lowering.Syntax
