import ModelicaParser.Invariant

/-! Reading a parsed syntax tree back from its printed tokens. The invariant
of every parsed tree (`Good`) fixes the lexical class of each retained token,
so the keywords and separators that delimit a node never occur inside a
subtree of another kind. Static semantics uses these lemmas to identify the
tree of a record's token sequence, without a second parse. -/
namespace Rumoca.Modelica.Good
open _root_.Parser AST

/-! ### Token classes of printed subtrees -/

/-- The literals an expression prints. -/
def expressionLiterals : List String :=
  ["(", ")", "[", "]", ",", ".", "+", "-", "*", "/", ".*", "der", "false", "true"]

/-- The further literals a declaration prints. -/
def declarationLiterals : List String := ["input", "output", "=", "each"]

/-- A literal token whose spelling is in `spellings`. -/
def spelledIn (spellings : List String) : Token → Bool
  | .literal s => spellings.contains s
  | _ => false

/-- A token an expression prints: a name token or an expression literal. -/
def ExpressionToken (t : Token) : Prop := Named t ∨ spelledIn expressionLiterals t = true

instance : DecidablePred ExpressionToken := fun t => by
  unfold ExpressionToken Named; infer_instance

/-- A token a declaration or equation prints. -/
def ElementToken (t : Token) : Prop :=
  ExpressionToken t ∨ spelledIn declarationLiterals t = true

instance : DecidablePred ElementToken := fun t => by
  unfold ElementToken; infer_instance

private theorem literal {s : String} (h : spelledIn expressionLiterals (.literal s) = true := by decide) :
    ExpressionToken (.literal s) := .inr h

private theorem operator_token {t : Token} (h : t ∈ operators) : ExpressionToken t := by
  simp only [operators, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> exact literal

mutual
  theorem expr_tokens : (e : Expr) → expr e → ∀ t ∈ Print.expr e, ExpressionToken t
    | .reference ref, valid => reference_tokens ref valid
    | .call function arguments, ⟨called, valid⟩ => by
      intro t member
      simp only [Print.expr, List.mem_append, or_assoc, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with member | rfl | member | rfl
      · exact callee_tokens function called t member
      · exact literal
      · exact exprs_tokens arguments valid t member
      · exact literal
    | .boolean value, valid => by
      intro t member
      simp only [Print.expr, List.mem_cons, List.not_mem_nil, or_false] at member
      subst member
      rcases valid with rfl | rfl <;> exact literal
    | .parens items, valid => by
      intro t member
      simp only [Print.expr, List.mem_append, or_assoc, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | member | rfl
      · exact literal
      · exact outputs_tokens items valid t member
      · exact literal
    | .unary operator operand, ⟨signed, valid⟩ => by
      intro t member
      simp only [Print.expr, List.mem_cons] at member
      rcases member with rfl | member
      · rcases signed with rfl | rfl <;> exact literal
      · exact expr_tokens operand valid t member
    | .binary operator left right, ⟨op, validLeft, validRight⟩ => by
      intro t member
      simp only [Print.expr, List.mem_append, List.mem_cons] at member
      rcases member with member | rfl | member
      · exact expr_tokens left validLeft t member
      · exact operator_token op
      · exact expr_tokens right validRight t member

  theorem callee_tokens : (c : Callee) → callee c → ∀ t ∈ Print.callee c, ExpressionToken t
    | .reference ref, valid => reference_tokens ref valid
    | .der, _ => by
      intro t member
      simp only [Print.callee, List.mem_cons, List.not_mem_nil, or_false] at member
      subst member
      exact literal

  theorem reference_tokens : (r : ComponentReference) → reference r →
      ∀ t ∈ Print.reference r, ExpressionToken t
    | ⟨global, parts⟩, ⟨_, valid⟩ => by
      intro t member
      cases global
      · simp only [Print.reference, Bool.false_eq_true, ↓reduceIte, List.nil_append] at member
        exact components_tokens parts valid t member
      · simp only [Print.reference, ↓reduceIte, List.cons_append, List.nil_append,
          List.mem_cons] at member
        rcases member with rfl | member
        · exact literal
        · exact components_tokens parts valid t member

  theorem components_tokens : (ps : List Part) → components ps →
      ∀ t ∈ Print.components ps, ExpressionToken t
    | [], _ => by simp [Print.components]
    | first :: rest, ⟨valid, following⟩ => by
      intro t member
      simp only [Print.components, List.mem_append] at member
      rcases member with member | member
      · exact component_tokens first valid t member
      · exact componentsTail_tokens rest following t member

  theorem componentsTail_tokens : (ps : List Part) → components ps →
      ∀ t ∈ Print.componentsTail ps, ExpressionToken t
    | [], _ => by simp [Print.componentsTail]
    | next :: rest, ⟨valid, following⟩ => by
      intro t member
      simp only [Print.componentsTail, List.mem_cons, List.mem_append, or_assoc] at member
      rcases member with rfl | member | member
      · exact literal
      · exact component_tokens next valid t member
      · exact componentsTail_tokens rest following t member

  theorem component_tokens : (p : Part) → component p → ∀ t ∈ Print.component p, ExpressionToken t
    | ⟨name, indices⟩, ⟨named, valid⟩ => by
      intro t member
      simp only [Print.component, List.mem_cons] at member
      rcases member with rfl | member
      · exact .inl named
      · exact subscripts_tokens indices valid t member

  theorem subscripts_tokens : (o : Option (List Expr)) → subscripts o →
      ∀ t ∈ Print.subscripts o, ExpressionToken t
    | none, _ => by simp [Print.subscripts]
    | some indices, valid => by
      intro t member
      simp only [Print.subscripts, List.mem_cons, List.mem_append, or_assoc, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | member | rfl
      · exact literal
      · exact exprs_tokens indices valid t member
      · exact literal

  theorem exprs_tokens : (es : List Expr) → exprs es → ∀ t ∈ Print.exprs es, ExpressionToken t
    | [], _ => by simp [Print.exprs]
    | first :: rest, ⟨valid, following⟩ => by
      intro t member
      simp only [Print.exprs, List.mem_append] at member
      rcases member with member | member
      · exact expr_tokens first valid t member
      · exact exprsTail_tokens rest following t member

  theorem exprsTail_tokens : (es : List Expr) → exprs es →
      ∀ t ∈ Print.exprsTail es, ExpressionToken t
    | [], _ => by simp [Print.exprsTail]
    | next :: rest, ⟨valid, following⟩ => by
      intro t member
      simp only [Print.exprsTail, List.mem_cons, List.mem_append, or_assoc] at member
      rcases member with rfl | member | member
      · exact literal
      · exact expr_tokens next valid t member
      · exact exprsTail_tokens rest following t member

  theorem outputs_tokens : (os : List (Option Expr)) → outputs os →
      ∀ t ∈ Print.outputs os, ExpressionToken t
    | [], _ => by simp [Print.outputs]
    | first :: rest, ⟨valid, following⟩ => by
      intro t member
      simp only [Print.outputs, List.mem_append] at member
      rcases member with member | member
      · exact output_tokens first valid t member
      · exact outputsTail_tokens rest following t member

  theorem outputsTail_tokens : (os : List (Option Expr)) → outputs os →
      ∀ t ∈ Print.outputsTail os, ExpressionToken t
    | [], _ => by simp [Print.outputsTail]
    | next :: rest, ⟨valid, following⟩ => by
      intro t member
      simp only [Print.outputsTail, List.mem_cons, List.mem_append, or_assoc] at member
      rcases member with rfl | member | member
      · exact literal
      · exact output_tokens next valid t member
      · exact outputsTail_tokens rest following t member

  theorem output_tokens : (o : Option Expr) → output o → ∀ t ∈ Print.output o, ExpressionToken t
    | none, _ => by simp [Print.output]
    | some value, valid => expr_tokens value valid
end

private theorem expression_element {t : Token} (h : ExpressionToken t) : ElementToken t := .inl h

private theorem element_literal {s : String}
    (h : spelledIn declarationLiterals (.literal s) = true := by decide) :
    ElementToken (.literal s) := .inr h

theorem name_tokens {n : Name} (valid : name n) : ∀ t ∈ Print.name n, ElementToken t := by
  obtain ⟨_, named⟩ := valid
  intro t member
  cases n with
  | nil => simp [Print.name] at member
  | cons first rest =>
    simp only [Print.name, List.mem_cons, List.mem_flatMap] at member
    rcases member with rfl | ⟨part, found, member⟩
    · exact expression_element (.inl (named _ (List.mem_cons_self ..)))
    · simp only [List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact expression_element literal
      · exact expression_element (.inl (named _ (List.mem_cons_of_mem _ found)))

mutual
  theorem modification_tokens : (m : Modification) → modification m →
      ∀ t ∈ Print.modification m, ElementToken t
    | .class arguments value, ⟨valid, bound⟩ => by
      intro t member
      simp only [Print.modification, List.mem_cons, List.mem_append, or_assoc] at member
      rcases member with rfl | member | rfl | member
      · exact expression_element literal
      · exact argumentList_tokens arguments valid t member
      · exact expression_element literal
      · exact binding_tokens value bound t member
    | .value value, valid => by
      intro t member
      simp only [Print.modification, List.mem_cons] at member
      rcases member with rfl | member
      · exact element_literal
      · exact expression_element (expr_tokens value valid t member)

  theorem binding_tokens : (o : Option Expr) → binding o → ∀ t ∈ Print.binding o, ElementToken t
    | none, _ => by simp [Print.binding]
    | some value, valid => by
      intro t member
      simp only [Print.binding, List.mem_cons] at member
      rcases member with rfl | member
      · exact element_literal
      · exact expression_element (expr_tokens value valid t member)

  theorem argumentList_tokens : (as : List Argument) → argumentList as →
      ∀ t ∈ Print.argumentList as, ElementToken t
    | [], _ => by simp [Print.argumentList]
    | first :: rest, ⟨valid, following⟩ => by
      intro t member
      simp only [Print.argumentList, List.mem_append] at member
      rcases member with member | member
      · exact argument_tokens first valid t member
      · exact argumentsTail_tokens rest following t member

  theorem argumentsTail_tokens : (as : List Argument) → argumentList as →
      ∀ t ∈ Print.argumentsTail as, ElementToken t
    | [], _ => by simp [Print.argumentsTail]
    | next :: rest, ⟨valid, following⟩ => by
      intro t member
      simp only [Print.argumentsTail, List.mem_cons, List.mem_append, or_assoc] at member
      rcases member with rfl | member | member
      · exact expression_element literal
      · exact argument_tokens next valid t member
      · exact argumentsTail_tokens rest following t member

  theorem argument_tokens : (a : Argument) → argument a → ∀ t ∈ Print.argument a, ElementToken t
    | ⟨each, target⟩, valid => by
      intro t member
      cases each
      · simp only [Print.argument, Bool.false_eq_true, ↓reduceIte, List.nil_append] at member
        exact elementModification_tokens target valid t member
      · simp only [Print.argument, ↓reduceIte, List.cons_append, List.nil_append,
          List.mem_cons] at member
        rcases member with rfl | member
        · exact element_literal
        · exact elementModification_tokens target valid t member

  theorem elementModification_tokens : (e : ElementModification) → elementModification e →
      ∀ t ∈ Print.elementModification e, ElementToken t
    | ⟨target, value⟩, ⟨named, valid⟩ => by
      intro t member
      simp only [Print.elementModification, List.mem_append] at member
      rcases member with member | member
      · exact name_tokens named t member
      · exact optionalModification_tokens value valid t member

  theorem optionalModification_tokens : (o : Option Modification) → optionalModification o →
      ∀ t ∈ Print.optionalModification o, ElementToken t
    | none, _ => by simp [Print.optionalModification]
    | some value, valid => modification_tokens value valid
end

theorem declaration_tokens {d : Declaration} (valid : declaration d) :
    ∀ t ∈ Print.declaration d, ElementToken t := by
  obtain ⟨named, indexed, modified⟩ := valid
  intro t member
  simp only [Print.declaration, List.cons_append, List.mem_cons, List.mem_append] at member
  rcases member with rfl | member | member
  · exact expression_element (.inl named)
  · exact expression_element (subscripts_tokens _ indexed t member)
  · exact optionalModification_tokens _ modified t member

theorem element_tokens {e : Element} (valid : element e) : ∀ t ∈ Print.element e, ElementToken t := by
  obtain ⟨⟨typePrefix', typeName, indices, declared⟩⟩ := e
  obtain ⟨prefixed, named, indexed, ⟨_, each⟩⟩ := valid
  intro t member
  simp only [Print.element, Print.componentClause, List.mem_append, or_assoc] at member
  rcases member with member | member | member | member
  · cases typePrefix' with
    | none => simp [Print.typePrefix] at member
    | some token =>
      simp [Print.typePrefix] at member
      subst member
      rcases prefixed _ rfl with h | h <;> rw [h] <;> exact element_literal
  · exact name_tokens named t member
  · exact expression_element (subscripts_tokens _ indexed t member)
  · cases declared with
    | nil => simp [Print.declarations] at member
    | cons first rest =>
      simp only [Print.declarations, List.mem_append, List.mem_flatMap, List.mem_cons] at member
      rcases member with member | ⟨d, found, rfl | member⟩
      · exact declaration_tokens (each _ (List.mem_cons_self ..)) t member
      · exact expression_element literal
      · exact declaration_tokens (each _ (List.mem_cons_of_mem _ found)) t member

theorem equation_tokens {e : Equation} (valid : equation e) :
    ∀ t ∈ Print.equation e, ElementToken t := by
  obtain ⟨left, right⟩ := e
  obtain ⟨validLeft, validRight⟩ := valid
  intro t member
  simp only [Print.equation, List.mem_append, List.mem_cons] at member
  rcases member with member | rfl | member
  · exact expression_element (expr_tokens _ validLeft t member)
  · exact element_literal
  · exact expression_element (expr_tokens _ validRight t member)

/-! ### Delimiters -/

/-- A token outside a token class does not occur in a subtree of that class. -/
theorem not_mem_of_tokens {P : Token → Prop} {tokens : List Token} {t : Token}
    (all : ∀ x ∈ tokens, P x) (outside : ¬ P t) : t ∉ tokens :=
  fun member => outside (all t member)

/-- The first occurrence of a delimiter absent from both prefixes splits two
equal lists at the same place. -/
theorem split_unique {α : Type} {x : α} {a b rest rest' : List α} (left : x ∉ a) (right : x ∉ b)
    (same : a ++ x :: rest = b ++ x :: rest') : a = b ∧ rest = rest' := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simpa using same
    | cons head tail =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at same
      exact absurd (same.1 ▸ List.mem_cons_self ..) right
  | cons head tail ih =>
    cases b with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at same
      exact absurd (same.1 ▸ List.mem_cons_self ..) left
    | cons head' tail' =>
      simp only [List.cons_append, List.cons.injEq] at same
      obtain ⟨rfl, same⟩ := same
      obtain ⟨rfl, rfl⟩ := ih (fun m => left (List.mem_cons_of_mem _ m))
        (fun m => right (List.mem_cons_of_mem _ m)) same
      exact ⟨rfl, rfl⟩

/-! ### Expressions -/

theorem not_named_literal {s : String} : ¬ Named (.literal s) := nofun

theorem component_ne_nil (p : Part) : Print.component p ≠ [] := by
  obtain ⟨_, _⟩ := p
  simp [Print.component]

theorem reference_ne_nil {r : ComponentReference} (valid : reference r) : Print.reference r ≠ [] := by
  obtain ⟨global, parts⟩ := r
  obtain ⟨nonempty, _⟩ := valid
  cases parts with
  | nil => exact absurd rfl nonempty
  | cons first _ =>
    have := component_ne_nil first
    cases global <;> simp_all [Print.reference, Print.components]

theorem expr_ne_nil {e : Expr} (valid : expr e) : Print.expr e ≠ [] := by
  cases e with
  | reference ref => exact reference_ne_nil valid
  | call | boolean | parens | unary | binary => simp [Print.expr]

theorem callee_ne_nil {c : Callee} (valid : callee c) : Print.callee c ≠ [] := by
  cases c with
  | reference ref => exact reference_ne_nil valid
  | der => simp [Print.callee]

/-- The first token of a printed reference is `.` or a name token. -/
theorem reference_head {r : ComponentReference} (valid : reference r) :
    ∃ head rest, Print.reference r = head :: rest ∧ (head = .literal "." ∨ Named head) := by
  obtain ⟨global, parts⟩ := r
  obtain ⟨nonempty, each⟩ := valid
  cases global
  · cases parts with
    | nil => exact absurd rfl nonempty
    | cons first rest =>
      obtain ⟨name, indices⟩ := first
      exact ⟨name, Print.subscripts indices ++ Print.componentsTail rest, rfl,
        .inr ((components_iff _).mp each _ (List.mem_cons_self ..)).1⟩
  · exact ⟨.literal ".", Print.components parts, rfl, .inl rfl⟩

/-- The expression printed as one name token is that bare name. -/
theorem bare_of_printed {e : Expr} {t : Token} (valid : expr e) (named : Named t)
    (printed : Print.expr e = [t]) : e = .reference ⟨false, [⟨t, none⟩]⟩ := by
  cases e with
  | reference ref =>
    obtain ⟨global, parts⟩ := ref
    obtain ⟨nonempty, _⟩ := valid
    cases global
    · cases parts with
      | nil => exact absurd rfl nonempty
      | cons first rest =>
        obtain ⟨name, indices⟩ := first
        have rest_nil := component_ne_nil
        cases indices <;> cases rest <;>
          simp_all [Print.expr, Print.reference, Print.components, Print.component,
            Print.subscripts, Print.componentsTail]
    · simp only [Print.expr, Print.reference, ↓reduceIte, List.cons_append, List.nil_append,
        List.cons.injEq] at printed
      rw [← printed.1] at named
      exact absurd named not_named_literal
  | call function arguments =>
    have length := congrArg List.length printed
    have := List.length_pos_of_ne_nil (callee_ne_nil valid.1)
    simp [Print.expr] at length
    omega
  | boolean value =>
    simp only [Print.expr, List.cons.injEq, and_true] at printed
    subst printed
    rcases valid with rfl | rfl <;> exact absurd named not_named_literal
  | parens items =>
    have length := congrArg List.length printed
    simp [Print.expr] at length
  | unary operator operand =>
    simp only [Print.expr, List.cons.injEq] at printed
    exact absurd printed.2 (expr_ne_nil valid.2)
  | binary operator left right =>
    have length := congrArg List.length printed
    have := List.length_pos_of_ne_nil (expr_ne_nil valid.2.1)
    simp [Print.expr] at length
    omega

/-- The expression printed as a sign and a name token is that signed name. -/
theorem signed_of_printed {e : Expr} {sign t : Token} (valid : expr e) (named : Named t)
    (signed : sign = .literal "+" ∨ sign = .literal "-") (printed : Print.expr e = [sign, t]) :
    e = .unary sign (.reference ⟨false, [⟨t, none⟩]⟩) := by
  have unnamed : ¬ Named sign ∧ sign ≠ .literal "." := by
    rcases signed with rfl | rfl <;> exact ⟨not_named_literal, by simp⟩
  cases e with
  | reference ref =>
    obtain ⟨head, rest, same, headed⟩ := reference_head valid
    simp only [Print.expr, same, List.cons.injEq] at printed
    rw [printed.1] at headed
    rcases headed with h | h
    · exact absurd h unnamed.2
    · exact absurd h unnamed.1
  | call function arguments =>
    cases function with
    | der =>
      simp only [Print.expr, Print.callee, List.cons_append, List.nil_append,
        List.cons.injEq] at printed
      rcases signed with rfl | rfl <;> simp at printed
    | reference ref =>
      obtain ⟨head, rest, same, headed⟩ := reference_head valid.1
      simp only [Print.expr, Print.callee, same, List.cons_append, List.cons.injEq] at printed
      rw [printed.1] at headed
      rcases headed with h | h
      · exact absurd h unnamed.2
      · exact absurd h unnamed.1
  | boolean value => simp [Print.expr] at printed
  | parens items =>
    simp only [Print.expr, List.cons_append, List.cons.injEq] at printed
    rcases signed with rfl | rfl <;> simp at printed
  | unary operator operand =>
    simp only [Print.expr, List.cons.injEq] at printed
    obtain ⟨rfl, printed⟩ := printed
    rw [bare_of_printed valid.2 named printed]
  | binary operator left right =>
    have nonempty := List.length_pos_of_ne_nil (expr_ne_nil valid.2.1)
    have nonempty' := List.length_pos_of_ne_nil (expr_ne_nil valid.2.2)
    have length := congrArg List.length printed
    simp [Print.expr] at length
    omega

/-- The expression printed as `der ( t )` is the derivative call of that name. -/
theorem derivative_of_printed {e : Expr} {t : Token} (valid : expr e) (named : Named t)
    (printed : Print.expr e = [.literal "der", .literal "(", t, .literal ")"]) :
    e = .call .der [.reference ⟨false, [⟨t, none⟩]⟩] := by
  cases e with
  | reference ref =>
    obtain ⟨head, rest, same, headed⟩ := reference_head valid
    simp only [Print.expr, same, List.cons.injEq] at printed
    rw [printed.1] at headed
    rcases headed with h | h
    · simp at h
    · exact absurd h not_named_literal
  | call function arguments =>
    cases function with
    | der =>
      simp only [Print.expr, Print.callee, List.cons_append, List.nil_append, List.cons.injEq,
        true_and] at printed
      obtain ⟨_, arguments_valid⟩ := valid
      cases arguments with
      | nil => simp [Print.exprs] at printed
      | cons first rest =>
        obtain ⟨firstValid, _⟩ := arguments_valid
        cases rest with
        | nil =>
          simp only [Print.exprs, Print.exprsTail, List.append_nil] at printed
          have single : Print.expr first = [t] := by
            have := congrArg List.dropLast printed
            simpa using this
          rw [bare_of_printed firstValid named single]
        | cons second more =>
          have comma : Token.literal "," ∈ [t, Token.literal ")"] := by
            rw [← printed]
            simp [Print.exprs, Print.exprsTail]
          simp only [List.mem_cons, List.not_mem_nil, or_false] at comma
          rcases comma with comma | comma
          · rw [← comma] at named
            exact absurd named not_named_literal
          · simp at comma
    | reference ref =>
      obtain ⟨head, rest, same, headed⟩ := reference_head valid.1
      simp only [Print.expr, Print.callee, same, List.cons_append, List.cons.injEq] at printed
      rw [printed.1] at headed
      rcases headed with h | h
      · simp at h
      · exact absurd h not_named_literal
  | boolean value => simp [Print.expr] at printed
  | parens items => simp [Print.expr] at printed
  | unary operator operand =>
    simp only [Print.expr, List.cons.injEq] at printed
    rcases valid.1 with h | h <;> rw [h] at printed <;> simp at printed
  | binary operator left right =>
    obtain ⟨op, _, _⟩ := valid
    have member : operator ∈ [Token.literal "der", .literal "(", t, .literal ")"] := by
      rw [← printed]; simp [Print.expr]
    simp only [operators, List.mem_cons, List.not_mem_nil, or_false] at op member
    rcases member with rfl | rfl | rfl | rfl
    · simp at op
    · simp at op
    · rcases op with rfl | rfl | rfl | rfl | rfl <;> exact absurd named not_named_literal
    · simp at op

/-! ### Declarations, equations and classes -/

theorem subscripts_nil {o : Option (List Expr)} (empty : Print.subscripts o = []) : o = none := by
  cases o <;> simp_all [Print.subscripts]

theorem optionalModification_nil {o : Option Modification}
    (empty : Print.optionalModification o = []) : o = none := by
  cases o with
  | none => rfl
  | some m => cases m <;> simp [Print.optionalModification, Print.modification] at empty

/-- The declaration printed as `T n` is the unprefixed, unmodified scalar
declaration of the name `n` with the one-token type `T`. -/
theorem element_of_printed {e : Element} {typeName t : Token} (valid : element e)
    (typeNamed : Named typeName) (printed : Print.element e = [typeName, t]) :
    e = .component ⟨none, [typeName], none, [⟨t, none, none⟩]⟩ := by
  obtain ⟨⟨typePrefix', typeNames, indices, declared⟩⟩ := e
  obtain ⟨prefixed, ⟨typeNonempty, _⟩, _, ⟨declaredNonempty, _⟩⟩ := valid
  cases typePrefix' with
  | some token =>
    simp only [Print.element, Print.componentClause, Print.typePrefix, Option.elim,
      List.cons_append, List.cons.injEq] at printed
    rw [← printed.1] at typeNamed
    rcases prefixed token rfl with h | h <;> rw [h] at typeNamed <;>
      exact absurd typeNamed not_named_literal
  | none =>
  cases typeNames with
  | nil => exact absurd rfl typeNonempty
  | cons first rest =>
  cases declared with
  | nil => exact absurd rfl declaredNonempty
  | cons d ds =>
  obtain ⟨dName, dIndices, dModification⟩ := d
  have length := congrArg List.length printed
  simp only [Print.element, Print.componentClause, Print.typePrefix, Option.elim, Print.name,
    Print.declarations, Print.declaration, List.nil_append, List.cons_append, List.append_assoc,
    List.length_cons, List.length_append, List.length_flatMap, List.length_nil] at length
  have restEmpty : rest = [] := by
    cases rest with
    | nil => rfl
    | cons _ _ => simp at length; omega
  have declaredEmpty : ds = [] := by
    cases ds with
    | nil => rfl
    | cons _ _ => simp at length; omega
  subst restEmpty declaredEmpty
  have indicesEmpty : indices = none :=
    subscripts_nil (List.length_eq_zero_iff.mp (by simp at length; omega))
  have dIndicesEmpty : dIndices = none :=
    subscripts_nil (List.length_eq_zero_iff.mp (by simp at length; omega))
  have dModificationEmpty : dModification = none :=
    optionalModification_nil (List.length_eq_zero_iff.mp (by simp at length; omega))
  subst indicesEmpty dIndicesEmpty dModificationEmpty
  simp only [Print.element, Print.componentClause, Print.typePrefix, Option.elim, Print.name,
    Print.declarations, Print.declaration, Print.subscripts, Print.optionalModification,
    List.flatMap_nil, List.nil_append, List.append_nil, List.cons_append, List.cons.injEq,
    and_true] at printed
  rw [printed.1, printed.2]

theorem not_expression_equals : ¬ ExpressionToken (.literal "=") := by decide

/-- An equation printed with its sides on either side of its only `=`. -/
theorem equation_of_printed {q : Equation} {left right : List Token} (valid : equation q)
    (leftFree : .literal "=" ∉ left)
    (printed : Print.equation q = left ++ .literal "=" :: right) :
    ∃ l r, q = .simple l r ∧ expr l ∧ expr r ∧ Print.expr l = left ∧ Print.expr r = right := by
  obtain ⟨l, r⟩ := q
  obtain ⟨validLeft, validRight⟩ := valid
  obtain ⟨sameLeft, sameRight⟩ := split_unique
    (not_mem_of_tokens (expr_tokens l validLeft) not_expression_equals) leftFree printed
  exact ⟨l, r, rfl, validLeft, validRight, sameLeft, sameRight⟩

/-- A token a class body prints. -/
def BodyToken (t : Token) : Prop :=
  ElementToken t ∨ t = .literal ";" ∨ t = .literal "equation"

instance : DecidablePred BodyToken := fun t => by
  unfold BodyToken; infer_instance

theorem elements_tokens {es : List Element} (valid : ∀ e ∈ es, element e) :
    ∀ t ∈ es.flatMap (fun e => Print.element e ++ [.literal ";"]),
      ElementToken t ∨ t = .literal ";" := by
  intro t member
  simp only [List.mem_flatMap, List.mem_append, List.mem_singleton] at member
  obtain ⟨e, found, member | rfl⟩ := member
  · exact .inl (element_tokens (valid e found) t member)
  · exact .inr rfl

theorem equations_tokens {qs : List Equation} (valid : ∀ q ∈ qs, equation q) :
    ∀ t ∈ qs.flatMap (fun q => Print.equation q ++ [.literal ";"]),
      ElementToken t ∨ t = .literal ";" := by
  intro t member
  simp only [List.mem_flatMap, List.mem_append, List.mem_singleton] at member
  obtain ⟨q, found, member | rfl⟩ := member
  · exact .inl (equation_tokens (valid q found) t member)
  · exact .inr rfl

theorem composition_tokens {c : Composition} (valid : composition c) :
    ∀ t ∈ Print.composition c, BodyToken t := by
  obtain ⟨elements, sections⟩ := c
  obtain ⟨validElements, validSections⟩ := valid
  intro t member
  simp only [Print.composition, List.mem_append] at member
  rcases member with member | member
  · rcases elements_tokens validElements t member with h | h
    · exact .inl h
    · exact .inr (.inl h)
  · obtain ⟨s, found, member⟩ := List.mem_flatMap.mp member
    simp only [Print.equationSection, List.mem_cons] at member
    rcases member with rfl | member
    · exact .inr (.inr rfl)
    · rcases equations_tokens (validSections s found) t member with h | h
      · exact .inl h
      · exact .inr (.inl h)

/-- A class body printed as declarations, the keyword `equation` and the
equations, with no other `equation` keyword, has exactly that one equation
section. -/
theorem composition_of_printed {c : Composition} {declared equated : List Token}
    (valid : composition c) (declaredFree : .literal "equation" ∉ declared)
    (equatedFree : .literal "equation" ∉ equated)
    (printed : Print.composition c = declared ++ .literal "equation" :: equated) :
    ∃ equations, c.sections = [⟨equations⟩] ∧
      c.elements.flatMap (fun e => Print.element e ++ [.literal ";"]) = declared ∧
      equations.flatMap (fun q => Print.equation q ++ [.literal ";"]) = equated := by
  obtain ⟨elements, sections⟩ := c
  obtain ⟨validElements, validSections⟩ := valid
  have elementsFree := not_mem_of_tokens (elements_tokens validElements)
    (t := .literal "equation") (by decide)
  cases sections with
  | nil =>
    simp only [Print.composition, List.flatMap_nil, List.append_nil] at printed
    exact absurd (printed ▸ List.mem_append_right _ (List.mem_cons_self ..)) elementsFree
  | cons first rest =>
    obtain ⟨equations⟩ := first
    simp only [Print.composition, List.flatMap_cons, Print.equationSection, List.cons_append]
      at printed
    obtain ⟨sameElements, sameEquations⟩ := split_unique elementsFree declaredFree printed
    cases rest with
    | nil => exact ⟨equations, rfl, sameElements, by simpa using sameEquations⟩
    | cons next more =>
      have member : Token.literal "equation" ∈ equated := by
        rw [← sameEquations]
        simp [Print.equationSection]
      exact absurd member equatedFree

/-- A stored definition printed as `model n B end e ;`, with no `end` in `B`, is
the one model class with that body. -/
theorem storedDefinition_of_printed {d : StoredDefinition} {first last : Token}
    {body : List Token} (valid : storedDefinition d) (bodyFree : .literal "end" ∉ body)
    (printed : Print.storedDefinition d =
      .literal "model" :: first :: body ++ [.literal "end", last, .literal ";"]) :
    ∃ c, d = ⟨[⟨.literal "model", .long first c last⟩]⟩ ∧ composition c ∧
      Print.composition c = body := by
  obtain ⟨classes⟩ := d
  cases classes with
  | nil => simp [Print.storedDefinition] at printed
  | cons definition rest =>
    obtain ⟨prefixes, ⟨first', c, last'⟩⟩ := definition
    obtain ⟨⟨rfl, _, validBody, _⟩, _⟩ := List.forall_mem_cons.mp valid
    simp only [Print.storedDefinition, List.flatMap_cons, Print.classDefinition,
      Print.classSpecifier, List.cons_append, List.append_assoc,
      List.cons.injEq, true_and] at printed
    obtain ⟨rfl, printed⟩ := printed
    obtain ⟨sameBody, rest'⟩ := split_unique
      (not_mem_of_tokens (composition_tokens validBody) (t := .literal "end") (by decide))
      bodyFree printed
    simp only [List.cons.injEq] at rest'
    obtain ⟨rfl, restEmpty⟩ := rest'
    cases rest with
    | nil => exact ⟨c, rfl, validBody, sameBody⟩
    | cons _ _ => simp at restEmpty

end Rumoca.Modelica.Good
