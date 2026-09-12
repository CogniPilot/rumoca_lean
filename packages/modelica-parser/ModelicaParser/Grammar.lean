import ModelicaParser.Generated
import ModelicaParser.AST

/-! Source grammar derivations for the current AST profiles. These use the
generated one-step EBNF equations, independently of LR execution. A recursive
source form can extend this layer with an induction over its syntax. -/
namespace Rumoca.Grammar
open _root_.Parser
open EBNF

theorem accepts_composition (body : List Symbol)
    (derivation : Derives Generated.sourceGrammar (.ref "composition") body) :
    Accepts Generated.sourceGrammar
      ([.literal "model", .ident] ++ body ++ [.literal "end", .ident, .literal ";"]) := by
  simp [Generated.start_rule, Generated.rule_stored_definition,
    Generated.rule_class_definition, Generated.rule_class_prefixes,
    Generated.rule_class_specifier, Generated.rule_long_class_specifier,
    Generated.rule_standard_class_specifier, Generated.rule_ident,
    Generated.rule_model, Generated.rule_end,
    Derives.seq_iff, Derives.terminal_iff, derivation]

theorem unit_in_grammar (m : AST.Model) :
    Accepts Generated.sourceGrammar (m.tokens.map Token.symbol) := by
  apply accepts_composition ((m.tokens.drop 2).take (m.tokens.length - 5) |>.map Token.symbol)
  simp [Generated.rule_composition, Generated.rule_unit_composition,
    Generated.rule_component_clause, Generated.rule_type_specifier,
    Generated.rule_component_list, Generated.rule_component_declaration,
    Generated.rule_declaration, Generated.rule_equation_section,
    Generated.rule_some_equation, Generated.rule_simple_equation,
    Generated.rule_component_reference, Generated.rule_ident,
    Generated.rule_equation, Generated.rule_der,
    Derives.seq_iff, Derives.alt_iff, Derives.terminal_iff, AST.Model.tokens, Token.symbol]

end Rumoca.Grammar
