import Parser.LALR.EBNFStructure

/-! Typed structural actions with recursive rule delegation. Rules are data
lookups, not inline expansions. Every recursive rule call consumes a named
node; semantic maps recurse only into a smaller action. No token recognition,
language AST, proof-only parser witness or caller-selected fuel is executed. -/
namespace Parser.LALR.Frontend.StructuralActions

inductive Action (Payload : Type) (Result : String → Type) : Type → Type 1 where
  | empty : Action Payload Result Unit
  | terminal (symbol : Parser.Symbol) : Action Payload Result Payload
  | seq (left : Action Payload Result α) (right : Action Payload Result β) :
      Action Payload Result (α × β)
  | alt (left right : Action Payload Result α) : Action Payload Result α
  | ref (name : String) : Action Payload Result (Result name)
  | map (f : α → β) (body : Action Payload Result α) : Action Payload Result β
  | optional (body : Action Payload Result α) : Action Payload Result (Option α)
  | many (body : Action Payload Result α) : Action Payload Result (List α)

def Action.expr : Action Payload Result α → EBNF.Expr
  | .empty => .terminal (.literal "")
  | .terminal s => .terminal s
  | .seq a b => .seq a.expr b.expr
  | .alt a b => .alt a.expr b.expr
  | .ref name => .ref name
  | .map _ a => a.expr
  | .optional a => .optional a.expr
  | .many a => .many a.expr

def Action.nodes : Action Payload Result α → Nat
  | .empty | .terminal _ | .ref _ => 1
  | .seq a b | .alt a b => 1 + a.nodes + b.nodes
  | .map _ a | .optional a | .many a => 1 + a.nodes

/-- Count structural nodes, excluding spellings, payload sizes and dormant
alternative metadata. This is a termination measure, not a complexity claim. -/
def nodes : Structure.Value Payload → Nat
  | .empty | .terminal _ _ | .optionalEmpty _ | .manyEmpty _ => 1
  | .named _ a | .altLeft _ a | .altRight _ a | .optionalSome a => 1 + nodes a
  | .seq a b | .manyCons a b => 1 + nodes a + nodes b

abbrev Rules (Payload : Type) (Result : String → Type) :=
  (name : String) → Option (Action Payload Result (Result name))

def run (rules : Rules Payload Result) (classify : Payload → Parser.Symbol)
    (a : Action Payload Result α) (v : Structure.Value Payload) : Option α :=
  match a with
  | .empty => match v with
    | .empty => some ()
    | _ => none
  | .terminal s => match v with
    | .terminal t payload => if t = s ∧ classify payload = s then some payload else none
    | _ => none
  | .seq a b => match v with
    | .seq x y => do return (← run rules classify a x, ← run rules classify b y)
    | _ => none
  | .alt a b => match v with
    | .altLeft other x => if other = b.expr then run rules classify a x else none
    | .altRight other y => if other = a.expr then run rules classify b y else none
    | _ => none
  | .ref name => match v with
    | .named other body =>
        if other = name then
          match rules name with
          | none => none
          | some rule => run rules classify rule body
        else none
    | _ => none
  | .map f a => (run rules classify a v).map f
  | .optional a => match v with
    | .optionalEmpty body => if body = a.expr then some none else none
    | .optionalSome body => (run rules classify a body).map some
    | _ => none
  | .many a => match v with
    | .manyEmpty body => if body = a.expr then some [] else none
    | .manyCons head tail => do
        return (← run rules classify a head) :: (← run rules classify (.many a) tail)
    | _ => none
termination_by (nodes v, a.nodes)
decreasing_by all_goals (simp_all [nodes, Action.nodes]; omega)

/-- Independent syntax-directed meaning, with typed rule lookup at named
children. The relation contains neither the executable nor an LR premise. -/
inductive Denotes (rules : Rules Payload Result) (classify : Payload → Parser.Symbol) :
    {α : Type} → Action Payload Result α → Structure.Value Payload → α → Prop where
  | empty : Denotes rules classify .empty .empty ()
  | terminal (same : classify payload = symbol) :
      Denotes rules classify (.terminal symbol) (.terminal symbol payload) payload
  | seq : Denotes rules classify a x left → Denotes rules classify b y right →
      Denotes rules classify (.seq a b) (.seq x y) (left, right)
  | altLeft : Denotes rules classify a x result →
      Denotes rules classify (.alt a b) (.altLeft b.expr x) result
  | altRight : Denotes rules classify b y result →
      Denotes rules classify (.alt a b) (.altRight a.expr y) result
  | ref (found : rules name = some rule) : Denotes rules classify rule body result →
      Denotes rules classify (.ref name) (.named name body) result
  | map : Denotes rules classify a v result →
      Denotes rules classify (.map f a) v (f result)
  | optionalEmpty : Denotes rules classify (.optional a) (.optionalEmpty a.expr) none
  | optionalSome : Denotes rules classify a v result →
      Denotes rules classify (.optional a) (.optionalSome v) (some result)
  | manyEmpty : Denotes rules classify (.many a) (.manyEmpty a.expr) []
  | manyCons : Denotes rules classify a head result →
      Denotes rules classify (.many a) tail rest →
      Denotes rules classify (.many a) (.manyCons head tail) (result :: rest)

theorem denotes_run (h : Denotes rules classify a v result) :
    run rules classify a v = some result := by
  induction h with
  | empty => simp [run]
  | terminal same => simp [run, same]
  | seq _ _ ih ih' => simp [run, ih, ih']
  | altLeft _ ih => simp [run, ih]
  | altRight _ ih => simp [run, ih]
  | ref found _ ih => simp [run, found, ih]
  | map _ ih => simp [run, ih]
  | optionalEmpty => simp [run]
  | optionalSome _ ih => simp [run, ih]
  | manyEmpty => simp [run]
  | manyCons _ _ ih ih' => simp [run, ih, ih']

theorem run_sound (a : Action Payload Result α) (v : Structure.Value Payload) (result : α)
    (success : run rules classify a v = some result) :
    Denotes rules classify a v result := by
  fun_induction run rules classify a v with
  | case1 => cases result; exact .empty
  | case2 _ _ => contradiction
  | case3 s t payload same =>
    obtain ⟨rfl, classified⟩ := same
    cases Option.some.inj success
    exact .terminal classified
  | case4 _ _ _ _ => contradiction
  | case5 _ _ _ => contradiction
  | case6 α β a b x y ih ih' =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at success
    obtain ⟨left, hl, right, hr, rfl⟩ := success
    exact .seq (ih left hl) (ih' right hr)
  | case7 _ _ _ _ _ _ => contradiction
  | case8 α a b x ih => exact .altLeft (ih result success)
  | case9 _ _ _ _ _ _ => contradiction
  | case10 α a b y ih => exact .altRight (ih result success)
  | case11 _ _ _ _ _ _ => contradiction
  | case12 _ _ _ _ _ _ => contradiction
  | case13 _ _ _ => contradiction
  | case14 name body rule found ih => exact .ref found (ih result success)
  | case15 _ _ _ _ => contradiction
  | case16 _ _ _ => contradiction
  | case17 v α β f a ih =>
    rw [Option.map_eq_some_iff] at success
    obtain ⟨before, executed, rfl⟩ := success
    exact .map (ih before executed)
  | case18 α a => cases Option.some.inj success; exact .optionalEmpty
  | case19 _ _ _ _ => contradiction
  | case20 α a body ih =>
    rw [Option.map_eq_some_iff] at success
    obtain ⟨before, executed, rfl⟩ := success
    exact .optionalSome (ih before executed)
  | case21 _ _ _ _ _ => contradiction
  | case22 α a => cases Option.some.inj success; exact .manyEmpty
  | case23 _ _ _ _ => contradiction
  | case24 α a head tail ih ih' =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at success
    obtain ⟨first, hf, rest, hr, rfl⟩ := success
    exact .manyCons (ih first hf) (ih' rest hr)
  | case25 _ _ _ _ _ => contradiction

theorem run_iff (a : Action Payload Result α) (v : Structure.Value Payload) (result : α) :
    run rules classify a v = some result ↔ Denotes rules classify a v result :=
  ⟨run_sound a v result, denotes_run⟩

def Action.WellFormed : Action Payload Result α → Prop
  | .empty | .ref _ => True
  | .terminal s => s ≠ .literal ""
  | .seq a b | .alt a b => a.WellFormed ∧ b.WellFormed
  | .map _ a | .optional a | .many a => a.WellFormed

/-- Every source production has its typed action, including all duplicate-name
entries. No acyclic rule-graph or bounded derivation-depth premise is used. -/
def Covers (g : EBNF.Grammar) (rules : Rules Payload Result) : Prop :=
  ∀ name e, (name, e) ∈ g →
    ∃ a, rules name = some a ∧ e = a.expr ∧ a.WellFormed

theorem total {rules : Rules Payload Result} {classify : Payload → Parser.Symbol}
    (covered : Covers g rules)
    (a : Action Payload Result α) (v : Structure.Value Payload)
    (wf : a.WellFormed) (valid : Structure.Valid g classify v)
    (shape : v.expr = a.expr) : ∃ result, Denotes rules classify a v result := by
  fun_induction run rules classify a v with
  | case1 => exact ⟨(), .empty⟩
  | case2 v bad => cases valid <;> simp_all [Action.expr, Structure.Value.expr]
  | case3 s t payload same =>
    obtain ⟨rfl, classified⟩ := same
    exact ⟨payload, .terminal classified⟩
  | case4 s t payload bad =>
    cases valid
    simp_all [Action.expr, Structure.Value.expr]
  | case5 v s bad =>
    cases valid <;> simp_all [Action.expr, Structure.Value.expr, Action.WellFormed]
  | case6 α β a b x y ih ih' =>
    cases valid with
    | seq vx vy =>
      obtain ⟨sx, sy⟩ := EBNF.Expr.seq.inj shape
      obtain ⟨left, hl⟩ := ih wf.1 vx sx
      obtain ⟨right, hr⟩ := ih' wf.2 vy sy
      exact ⟨(left, right), .seq hl hr⟩
  | case7 v α β a b bad => cases valid <;> simp_all [Action.expr, Structure.Value.expr]
  | case8 α a b x ih =>
    cases valid with
    | altLeft vx =>
      obtain ⟨result, h⟩ := ih wf.1 vx (EBNF.Expr.alt.inj shape).1
      exact ⟨result, .altLeft h⟩
  | case9 α a b other x bad => exact False.elim (bad (EBNF.Expr.alt.inj shape).2)
  | case10 α a b y ih =>
    cases valid with
    | altRight vy =>
      obtain ⟨result, h⟩ := ih wf.2 vy (EBNF.Expr.alt.inj shape).2
      exact ⟨result, .altRight h⟩
  | case11 α a b other y bad => exact False.elim (bad (EBNF.Expr.alt.inj shape).1)
  | case12 v α a b badLeft badRight =>
    cases valid <;> simp_all [Action.expr, Structure.Value.expr]
  | case13 name body missing =>
    cases valid with
    | named member vb =>
      obtain ⟨rule, found, _, _⟩ := covered name body.expr member
      simp_all
  | case14 name body rule found ih =>
    cases valid with
    | named member vb =>
      obtain ⟨expected, he, se, we⟩ := covered name body.expr member
      have same := Option.some.inj (he.symm.trans found)
      subst expected
      obtain ⟨result, h⟩ := ih we vb se
      exact ⟨result, .ref found h⟩
  | case15 name other body bad => exact False.elim (bad (EBNF.Expr.ref.inj shape))
  | case16 v name bad => cases valid <;> simp_all [Action.expr, Structure.Value.expr]
  | case17 v α β f a ih =>
    obtain ⟨result, h⟩ := ih wf valid shape
    exact ⟨f result, .map h⟩
  | case18 α a => exact ⟨none, .optionalEmpty⟩
  | case19 α a body bad => exact False.elim (bad (EBNF.Expr.optional.inj shape))
  | case20 α a body ih =>
    cases valid with
    | optionalSome vb =>
      obtain ⟨result, h⟩ := ih wf vb (EBNF.Expr.optional.inj shape)
      exact ⟨some result, .optionalSome h⟩
  | case21 v α a badEmpty badSome =>
    cases valid <;> simp_all [Action.expr, Structure.Value.expr]
  | case22 α a => exact ⟨[], .manyEmpty⟩
  | case23 α a body bad => exact False.elim (bad (EBNF.Expr.many.inj shape))
  | case24 α a head tail ih ih' =>
    cases valid with
    | manyCons vh vt st =>
      have sh := EBNF.Expr.many.inj shape
      obtain ⟨first, hf⟩ := ih wf vh sh
      obtain ⟨rest, hr⟩ := ih' wf vt (st.trans (congrArg EBNF.Expr.many sh))
      exact ⟨first :: rest, .manyCons hf hr⟩
  | case25 v α a badEmpty badCons =>
    cases valid <;> simp_all [Action.expr, Structure.Value.expr]

/-- Successful rule lookup may only introduce a declared source production. -/
def Licensed (g : EBNF.Grammar) (rules : Rules Payload Result) : Prop :=
  ∀ name a, rules name = some a → (name, a.expr) ∈ g ∧ a.WellFormed

theorem denotes_expr (h : Denotes rules classify a v result) : v.expr = a.expr := by
  induction h with
  | empty | terminal _ | ref _ _ _ | optionalEmpty | manyEmpty => rfl
  | seq _ _ ih ih' => simp [Structure.Value.expr, Action.expr, ih, ih']
  | altLeft _ ih | altRight _ ih | map _ ih | optionalSome _ ih =>
    simp [Structure.Value.expr, Action.expr, ih]
  | manyCons _ _ ih _ => simp [Structure.Value.expr, Action.expr, ih]

theorem denotes_valid {rules : Rules Payload Result} {classify : Payload → Parser.Symbol}
    (licensed : Licensed g rules) (h : Denotes rules classify a v result)
    (wf : a.WellFormed) : Structure.Valid g classify v := by
  induction h with
  | empty => exact .empty
  | terminal same => exact .terminal same wf
  | seq _ _ ih ih' => exact .seq (ih wf.1) (ih' wf.2)
  | altLeft _ ih => exact .altLeft (ih wf.1)
  | altRight _ ih => exact .altRight (ih wf.2)
  | ref found h ih =>
    obtain ⟨member, well⟩ := licensed _ _ found
    exact .named (denotes_expr h ▸ member) (ih well)
  | map _ ih => exact ih wf
  | optionalEmpty => exact .optionalEmpty
  | optionalSome _ ih => exact .optionalSome (ih wf)
  | manyEmpty => exact .manyEmpty
  | manyCons h h' ih ih' =>
    exact .manyCons (ih wf) (ih' wf)
      ((denotes_expr h').trans (congrArg EBNF.Expr.many (denotes_expr h).symm))

theorem domain {rules : Rules Payload Result} {classify : Payload → Parser.Symbol}
    (covered : Covers g rules) (licensed : Licensed g rules)
    (a : Action Payload Result α) (wf : a.WellFormed) (v : Structure.Value Payload) :
    (∃ result, run rules classify a v = some result) ↔
      Structure.Valid g classify v ∧ v.expr = a.expr := by
  constructor
  · rintro ⟨result, success⟩
    have h := run_sound a v result success
    exact ⟨denotes_valid licensed h wf, denotes_expr h⟩
  · rintro ⟨valid, shape⟩
    obtain ⟨result, h⟩ := total covered a v wf valid shape
    exact ⟨result, denotes_run h⟩

theorem unique (h : Denotes rules classify a v x) (h' : Denotes rules classify a v y) :
    x = y := Option.some.inj ((denotes_run h).symm.trans (denotes_run h'))

/-- The executable uses only the token parser, computable structural annotations
and typed rule table. The lowering witness is absent from runtime inputs. -/
def parse (parser : TokenParser Payload) (decode : Nat → Parser.Symbol)
    (annotations : Array AnnotatedRule) (rules : Rules Payload Result)
    (name : String) (tokens : List Payload) : Option (Result name) :=
  (Structure.parse parser decode annotations tokens).bind
    (run rules (decode ∘ parser.encode) (.ref name))

theorem parse_total {w : Witness} (parser : TokenParser Payload) (p : Prepared)
    (decode : Nat → Parser.Symbol) (annotations : Array AnnotatedRule)
    (rules : Rules Payload Result) (name : String)
    (grammar : parser.grammar = p.grammar) (decoder : decode = p.decode)
    (exactRules : annotations = w.rules) (checked : w.Conditions ((name, body) :: tail) p)
    (covered : Covers ((name, body) :: tail) rules)
    (parsed : parser.run tokens = .ok tree) :
    ∃ result, parse parser decode annotations rules name tokens = some result := by
  obtain ⟨v, success, root⟩ :=
    Structure.parse_total parser p decode annotations grammar decoder exactRules checked parsed
  obtain ⟨other, e, rest, source, shape, valid, _⟩ := root.2.2
  cases source
  obtain ⟨result, h⟩ := total covered (.ref name) v trivial valid shape
  exact ⟨result, by simp only [parse, success, Option.bind_some, denotes_run h]⟩

/-- Success retains the actual CST execution and payload-preserving structural
root, as well as the independent typed action meaning. -/
theorem parse_sound {w : Witness} (parser : TokenParser Payload) (p : Prepared)
    (decode : Nat → Parser.Symbol) (annotations : Array AnnotatedRule)
    (rules : Rules Payload Result) (name : String)
    (grammar : parser.grammar = p.grammar) (decoder : decode = p.decode)
    (exactRules : annotations = w.rules) (checked : w.Conditions source p)
    {result : Result name}
    (success : parse parser decode annotations rules name tokens = some result) :
    ∃ tree v, parser.run tokens = .ok tree ∧
      Structure.Root source p.grammar.start decode parser.encode annotations tree tokens v ∧
      Denotes rules (decode ∘ parser.encode) (.ref name) v result := by
  rw [parse, Option.bind_eq_some_iff] at success
  obtain ⟨v, structural, action⟩ := success
  obtain ⟨tree, parsed, root⟩ :=
    Structure.parse_sound parser p decode annotations grammar decoder exactRules checked structural
  exact ⟨tree, v, parsed, root, run_sound _ _ _ action⟩

/-- Complete-language preservation for the actual LALR parser. Recursive source
rules require only a covering table, never a derivation-depth bound. -/
theorem parse_accepts_iff {w : Witness} (parser : TokenParser Payload) (p : Prepared)
    (decode : Nat → Parser.Symbol) (annotations : Array AnnotatedRule)
    (rules : Rules Payload Result) (name : String)
    (grammar : parser.grammar = p.grammar) (decoder : decode = p.decode)
    (exactRules : annotations = w.rules) (checked : w.Conditions ((name, body) :: tail) p)
    (covered : Covers ((name, body) :: tail) rules) :
    (∃ result, parse parser decode annotations rules name tokens = some result) ↔
      parser.grammar.Accepts (tokens.map parser.encode) := by
  constructor
  · rintro ⟨result, success⟩
    obtain ⟨tree, _, parsed, _, _⟩ :=
      parse_sound parser p decode annotations rules name grammar decoder exactRules checked success
    exact (parser.accepts_iff tokens).mpr ⟨tree, parsed⟩
  · intro accepted
    obtain ⟨tree, parsed⟩ := (parser.accepts_iff tokens).mp accepted
    exact parse_total parser p decode annotations rules name grammar decoder exactRules checked
      covered parsed

end Parser.LALR.Frontend.StructuralActions

