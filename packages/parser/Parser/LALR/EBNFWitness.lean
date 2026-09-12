import Parser.EBNF.Semantics
import Parser.LALR.Grammar

/-! Finite structural witnesses for EBNF desugaring. Sequences remain inline;
references and helpers retain nonterminal identities. Witnesses describe local
syntactic obligations, not an assumed language-equivalence result. They are
preprocessing certificates and need not be retained in the generated parser. -/
namespace Parser.LALR.Frontend

structure Prepared where
  alphabet : Array Parser.Symbol
  names : Array String
  grammar : Grammar
  deriving Repr, DecidableEq

/-- Unknown tokens have their own out-of-range code, distinct from EOF. -/
def Prepared.encode (p : Prepared) (symbol : Parser.Symbol) : Nat :=
  (p.alphabet.findIdx? (· == symbol)).getD (p.alphabet.size + 1)

inductive Fragment where
  | empty
  | terminal (symbol : Parser.Symbol) (code : Nat)
  | ref (name : String) (nonterminal : Nat)
  | seq (left right : Fragment)
  | alt (nonterminal : Nat) (left right : Fragment)
  | optional (nonterminal : Nat) (body : Fragment)
  | many (nonterminal : Nat) (body : Fragment)
  deriving Repr, DecidableEq

def Fragment.expr : Fragment → EBNF.Expr
  | .empty => .terminal (.literal "")
  | .terminal s _ => .terminal s
  | .ref name _ => .ref name
  | .seq a b => .seq a.expr b.expr
  | .alt _ a b => .alt a.expr b.expr
  | .optional _ a => .optional a.expr
  | .many _ a => .many a.expr

def Fragment.rhs : Fragment → List Atom
  | .empty => []
  | .terminal _ t => [.terminal t]
  | .ref _ n | .alt n _ _ | .optional n _ | .many n _ => [.nonterminal n]
  | .seq a b => a.rhs ++ b.rhs

/-- Meanings assign source expressions to CFG nonterminals and reject
conflicting aliases. Fresh helper allocation is a construction policy;
sharing helpers with identical meanings need not change the proof contract. -/
abbrev Meanings := Array EBNF.Expr

/-- Interpretation of an inlined fragment. Only the sequence case recurses:
helper bodies are checked separately through their annotated productions. -/
def Fragment.Interprets (p : Prepared) (meanings : Meanings) : Fragment → Prop
  | .empty => True
  | .terminal s t => p.alphabet[t]? = some s ∧ p.encode s = t ∧ s ≠ .literal ""
  | .ref name n => meanings[n]? = some (.ref name)
  | .seq a b => a.Interprets p meanings ∧ b.Interprets p meanings
  | .alt n a b => meanings[n]? = some (.alt a.expr b.expr)
  | .optional n a => meanings[n]? = some (.optional a.expr)
  | .many n a => meanings[n]? = some (.many a.expr)

instance instDecidableInterprets (p : Prepared) (meanings : Meanings) (f : Fragment) :
    Decidable (f.Interprets p meanings) := by
  cases f with
  | seq a b =>
    haveI := instDecidableInterprets p meanings a
    haveI := instDecidableInterprets p meanings b
    exact inferInstanceAs (Decidable (_ ∧ _))
  | empty => exact inferInstanceAs (Decidable True)
  | terminal s t => exact inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | ref _ _ | alt _ _ _ | optional _ _ | many _ _ =>
    exact inferInstanceAs (Decidable (_ = _))
termination_by structural f

/-- Every structural alternative must occur in the actual CFG. The reference
case also binds the named nonterminal to its source rule slot. -/
def Fragment.Covered (source : EBNF.Grammar) (g : Grammar) : Fragment → Prop
  | .empty | .terminal _ _ | .seq _ _ => True
  | .ref name n => (source[n]?).map Prod.fst = some name
  | .alt n a b => ContextFreeRule.mk n a.rhs ∈ g.productions ∧
      ContextFreeRule.mk n b.rhs ∈ g.productions
  | .optional n a => ContextFreeRule.mk n [] ∈ g.productions ∧
      ContextFreeRule.mk n a.rhs ∈ g.productions
  | .many n a => ContextFreeRule.mk n [] ∈ g.productions ∧
      ContextFreeRule.mk n (a.rhs ++ [.nonterminal n]) ∈ g.productions

instance (source : EBNF.Grammar) (g : Grammar) (f : Fragment) :
    Decidable (f.Covered source g) := by
  cases f <;> simp only [Fragment.Covered] <;> infer_instance

/-- Unlike `Interprets`, this checks every nested fragment. -/
def Fragment.Checked (source : EBNF.Grammar) (p : Prepared) (meanings : Meanings) :
    Fragment → Prop
  | f@(.empty) | f@(.terminal _ _) | f@(.ref _ _) =>
      f.Interprets p meanings ∧ f.Covered source p.grammar
  | .seq a b => a.Checked source p meanings ∧ b.Checked source p meanings
  | f@(.alt _ a b) =>
      f.Interprets p meanings ∧ f.Covered source p.grammar ∧
        a.Checked source p meanings ∧ b.Checked source p meanings
  | f@(.optional _ a) | f@(.many _ a) =>
      f.Interprets p meanings ∧ f.Covered source p.grammar ∧ a.Checked source p meanings

instance instDecidableChecked (source : EBNF.Grammar) (p : Prepared)
    (meanings : Meanings) (f : Fragment) : Decidable (f.Checked source p meanings) := by
  cases f with
  | empty | terminal _ _ | ref _ _ => unfold Fragment.Checked; infer_instance
  | seq a b | alt _ a b =>
    haveI := instDecidableChecked source p meanings a
    haveI := instDecidableChecked source p meanings b
    unfold Fragment.Checked
    infer_instance
  | optional _ a | many _ a =>
    haveI := instDecidableChecked source p meanings a
    unfold Fragment.Checked
    infer_instance
termination_by structural f

inductive AnnotatedRule where
  | named (n : Nat) (name : String) (body : Fragment)
  | altLeft (n : Nat) (left right : Fragment)
  | altRight (n : Nat) (left right : Fragment)
  | optionalEmpty (n : Nat) (body : Fragment)
  | optionalSome (n : Nat) (body : Fragment)
  | manyEmpty (n : Nat) (body : Fragment)
  | manyCons (n : Nat) (body : Fragment)
  deriving Repr, DecidableEq

def AnnotatedRule.production : AnnotatedRule → Production
  | .named n _ a | .altLeft n a _ | .altRight n _ a | .optionalSome n a => ⟨n, a.rhs⟩
  | .optionalEmpty n _ | .manyEmpty n _ => ⟨n, []⟩
  | .manyCons n a => ⟨n, a.rhs ++ [.nonterminal n]⟩

def AnnotatedRule.meaning : AnnotatedRule → EBNF.Expr
  | .named _ name _ => .ref name
  | .altLeft _ a b | .altRight _ a b => .alt a.expr b.expr
  | .optionalEmpty _ a | .optionalSome _ a => .optional a.expr
  | .manyEmpty _ a | .manyCons _ a => .many a.expr

def AnnotatedRule.Valid (source : EBNF.Grammar) (p : Prepared) (meanings : Meanings)
    (rule : AnnotatedRule) : Prop :=
  meanings[rule.production.input]? = some rule.meaning ∧
    match rule with
    | .named _ name a => (name, a.expr) ∈ source ∧ a.Interprets p meanings
    | .altLeft _ a _ | .altRight _ _ a | .optionalSome _ a | .manyCons _ a =>
        a.Interprets p meanings
    | .optionalEmpty _ _ | .manyEmpty _ _ => True

instance (source : EBNF.Grammar) (p : Prepared) (meanings : Meanings) (r : AnnotatedRule) :
    Decidable (r.Valid source p meanings) := by
  cases r <;> simp only [AnnotatedRule.Valid] <;> infer_instance

/-- All conditions are finite and decidable. Coverage forbids missing source
branches; exact production equality forbids extra target rules. Source rule
names determine bodies uniquely, as required by the EBNF reader. -/
structure Witness where
  meanings : Meanings
  roots : Array Fragment
  rules : Array AnnotatedRule
  deriving Repr

def Witness.Conditions (source : EBNF.Grammar) (p : Prepared) (w : Witness) : Prop :=
  source ≠ [] ∧
  p.grammar.start = 0 ∧
  p.grammar.terminals = p.alphabet.size ∧
  w.roots.size = source.length ∧
  (∀ a ∈ source, ∀ b ∈ source, a.1 = b.1 → a.2 = b.2) ∧
  (∀ i : Fin source.length,
    w.meanings[i.val]? = some (.ref source[i].1) ∧
    ∃ f ∈ w.roots[i.val]?.toList,
      f.expr = source[i].2 ∧ f.Checked source p w.meanings ∧
      ContextFreeRule.mk i.val f.rhs ∈ p.grammar.productions) ∧
  (∀ rule ∈ w.rules, rule.Valid source p w.meanings) ∧
  p.grammar.productions = w.rules.map AnnotatedRule.production

instance (source : EBNF.Grammar) (p : Prepared) (w : Witness) :
    Decidable (w.Conditions source p) := by
  unfold Witness.Conditions
  infer_instance

def Witness.validate (source : EBNF.Grammar) (p : Prepared) (w : Witness) : Bool :=
  decide (w.Conditions source p)

theorem Witness.validate_iff {w : Witness} {source : EBNF.Grammar} {p : Prepared} :
    w.validate source p = true ↔ w.Conditions source p := by
  simp only [Witness.validate, decide_eq_true_eq]

end Parser.LALR.Frontend
