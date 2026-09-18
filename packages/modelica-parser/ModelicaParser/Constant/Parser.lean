import ModelicaParser.Actions
import ModelicaParser.Grammar
import ModelicaParser.Constant.Syntax

open _root_.Parser

namespace Rumoca.ConstantProfile
open EBNF Rumoca.Generated

/-! Grammar membership for the constant-rate profile. The declaration and
equation lists derive the left-recursive `constant_component_list` and
`constant_equation_list` productions by induction on the list, so the generic
EBNF recognizer accepts every model of the typed AST rather than a fixed
example. -/

private theorem declSymbols (s : String) :
    (declTokens s).map Token.symbol = [.literal "Real", .ident, .literal ";"] := rfl

private theorem eqSymbols (e : Equation) :
    (equationTokens e).map Token.symbol =
      [.literal "der", .literal "(", .ident, .literal ")", .literal "=", .ident, .literal ";"] := rfl

private theorem term (s : Symbol) (h : s ≠ .literal "") :
    Derives sourceGrammar (.terminal s) [s] := .terminal h

/-- One `Real ident` clause derives its two symbols. -/
private theorem clauseDerives :
    Derives sourceGrammar (.ref "component_clause") [.literal "Real", .ident] :=
  (rule_component_clause _).mpr <| Derives.seq_iff.mpr
    ⟨[.literal "Real"], [.ident],
      (rule_type_specifier _).mpr (term _ (by decide)),
      (rule_component_list _).mpr <| (rule_component_declaration _).mpr <|
        (rule_declaration _).mpr <| (rule_ident _).mpr (term _ (by decide)), rfl⟩

/-- A declaration group `Real ident ;` as the body of `constant_component_list`. -/
private theorem clauseSemiDerives (s : String) :
    Derives sourceGrammar
      (.seq (.ref "component_clause") (.terminal (.literal ";")))
      ((declTokens s).map Token.symbol) := by
  rw [declSymbols]
  exact Derives.seq_iff.mpr ⟨[.literal "Real", .ident], [.literal ";"], clauseDerives,
    term _ (by decide), rfl⟩

/-- One `der ( ident ) = ident ;` group as the body of `constant_equation_list`. -/
private theorem equationSemiDerives (e : Equation) :
    Derives sourceGrammar
      (.seq (.ref "constant_equation") (.terminal (.literal ";")))
      ((equationTokens e).map Token.symbol) := by
  rw [eqSymbols]
  refine Derives.seq_iff.mpr ⟨[.literal "der", .literal "(", .ident, .literal ")",
    .literal "=", .ident], [.literal ";"], (rule_constant_equation _).mpr ?_, term _ (by decide), rfl⟩
  refine Derives.seq_iff.mpr ⟨[.literal "der"], _, (rule_der _).mpr (term _ (by decide)), ?_, rfl⟩
  refine Derives.seq_iff.mpr ⟨[.literal "("], _, term _ (by decide), ?_, rfl⟩
  refine Derives.seq_iff.mpr ⟨[.ident], _,
    (rule_component_reference _).mpr ((rule_ident _).mpr (term _ (by decide))), ?_, rfl⟩
  refine Derives.seq_iff.mpr ⟨[.literal ")"], _, term _ (by decide), ?_, rfl⟩
  exact Derives.seq_iff.mpr ⟨[.literal "="], [.ident], term _ (by decide),
    (rule_real_literal _).mpr (term _ (by decide)), rfl⟩

/-- The nonempty declaration list derives `constant_component_list`. -/
private theorem componentListDerives (ss : List String) (hne : ss ≠ []) :
    Derives sourceGrammar (.ref "constant_component_list")
      ((ss.flatMap declTokens).map Token.symbol) := by
  induction ss using List.reverseRecOn with
  | nil => exact absurd rfl hne
  | append_singleton xs x ih =>
      rw [List.flatMap_append, List.map_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      by_cases hxs : xs = []
      · subst hxs
        simp only [List.flatMap_nil, List.map_nil, List.nil_append]
        exact (rule_constant_component_list _).mpr (.altLeft (clauseSemiDerives x))
      · exact (rule_constant_component_list _).mpr (.altRight (.seq (ih hxs) (clauseSemiDerives x)))

/-- The nonempty equation list derives `constant_equation_list`. -/
private theorem equationListDerives (es : List Equation) (hne : es ≠ []) :
    Derives sourceGrammar (.ref "constant_equation_list")
      ((es.flatMap equationTokens).map Token.symbol) := by
  induction es using List.reverseRecOn with
  | nil => exact absurd rfl hne
  | append_singleton xs x ih =>
      rw [List.flatMap_append, List.map_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      by_cases hxs : xs = []
      · subst hxs
        simp only [List.flatMap_nil, List.map_nil, List.nil_append]
        exact (rule_constant_equation_list _).mpr (.altLeft (equationSemiDerives x))
      · exact (rule_constant_equation_list _).mpr (.altRight (.seq (ih hxs) (equationSemiDerives x)))

theorem in_grammar (m : Model) :
    EBNF.Accepts Generated.sourceGrammar (m.tokens.map Token.symbol) := by
  have layout : m.tokens.map Token.symbol =
      [.literal "model", .ident] ++
        ((m.states.flatMap declTokens).map Token.symbol ++ [.literal "equation"] ++
          (m.equations.flatMap equationTokens).map Token.symbol) ++
        [.literal "end", .ident, .literal ";"] := by
    simp only [Model.tokens, List.map_append, List.map_cons, List.map_nil, Token.symbol,
      List.append_assoc, List.cons_append, List.nil_append]
  rw [layout]
  apply Rumoca.Grammar.accepts_composition
  rw [Generated.rule_composition]
  refine .altRight (.altRight (.altRight ((rule_constant_composition _).mpr ?_)))
  -- constant_composition: component_clause ';' constant_component_list constant_equation_section.
  -- The states split as the first clause plus the (nonempty) list of the rest.
  have hstates : m.states.flatMap declTokens =
      declTokens m.state0 ++ (m.state1 :: m.statesRest).flatMap declTokens := by
    simp [Model.states, List.flatMap_cons]
  rw [hstates, List.map_append, declSymbols]
  refine Derives.seq_iff.mpr ⟨[.literal "Real", .ident],
    .literal ";" :: (((m.state1 :: m.statesRest).flatMap declTokens).map Token.symbol ++
      [.literal "equation"] ++ (m.equations.flatMap equationTokens).map Token.symbol),
    clauseDerives, ?_, rfl⟩
  refine Derives.seq_iff.mpr ⟨[.literal ";"],
    ((m.state1 :: m.statesRest).flatMap declTokens).map Token.symbol ++
      [.literal "equation"] ++ (m.equations.flatMap equationTokens).map Token.symbol,
    term _ (by decide), ?_, rfl⟩
  refine Derives.seq_iff.mpr ⟨((m.state1 :: m.statesRest).flatMap declTokens).map Token.symbol,
    [.literal "equation"] ++ (m.equations.flatMap equationTokens).map Token.symbol,
    componentListDerives (m.state1 :: m.statesRest) (by simp), ?_, List.append_assoc _ _ _⟩
  rw [rule_constant_equation_section]
  exact Derives.seq_iff.mpr ⟨[.literal "equation"],
    (m.equations.flatMap equationTokens).map Token.symbol,
    (rule_equation _).mpr (term _ (by decide)),
    equationListDerives m.equations (by simp [Model.equations]), rfl⟩

def actions : ParserActions.Actions Model :=
  ⟨Model.tokens, decode, decode_sound, decode_complete, in_grammar⟩

abbrev Parsed := ParserActions.Parsed actions
def parse := ParserActions.parse actions

end Rumoca.ConstantProfile
