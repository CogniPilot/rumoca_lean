import ModelicaParser.Generated
import Parser.EBNF.Equivalence

/-! The two left-factored productions of `grammar/Modelica.ebnf` denote the
same words as their MLS 3.7 Appendix A forms (pinned annex
`build/modelica-3.7-syntax-reference.html`). Each annex form begins with an
optional part before an `IDENT`-initial remainder, which is not LR(1) under
the checked EBNF lowering once named arguments are admitted; the grammar
writes the alternative with and without that part instead. -/
namespace Rumoca.Modelica.Annex
open _root_.Parser EBNF

/-- `arithmetic-expression : [ add-operator ] term { add-operator term }`
(annex lines 1243-1247). -/
def arithmeticExpression : Expr :=
  .seq (.optional (.ref "add_operator"))
    (.seq (.ref "term") (.many (.seq (.ref "add_operator") (.ref "term"))))

/-- `component-reference : [ "." ] IDENT [ array-subscripts ]
{ "." IDENT [ array-subscripts ] }` (annex lines 1363-1367). -/
def componentReference : Expr :=
  .seq (.optional (.terminal (.literal ".")))
    (.seq (.terminal .ident) (.seq (.optional (.ref "array_subscripts"))
      (.many (.seq (.terminal (.literal ".")) (.seq (.terminal .ident)
        (.optional (.ref "array_subscripts")))))))

theorem arithmetic_expression_iff (word : List Symbol) :
    Derives Generated.sourceGrammar arithmeticExpression word ↔
      Derives Generated.sourceGrammar (.ref "arithmetic_expression") word := by
  rw [Generated.rule_arithmetic_expression]
  exact Derives.optional_seq_iff

theorem component_reference_iff (word : List Symbol) :
    Derives Generated.sourceGrammar componentReference word ↔
      Derives Generated.sourceGrammar (.ref "component_reference") word := by
  rw [Generated.rule_component_reference]
  exact Derives.optional_seq_iff

end Rumoca.Modelica.Annex
