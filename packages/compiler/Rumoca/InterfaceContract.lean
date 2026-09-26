import RumocaFMI3.DeclaredMetadata
import ModelicaParser.Lexer

/-! The exported-interface contract shared by the FMI 3 source-build contracts.

The declarations are the ones read back from the tokens lexed from the source
text (every `Real` declaration, the causality of its `input`/`output` prefix and
its written subscript); every name they read is declared. The model description
exports exactly those declarations (names, causalities and dimensions, in source
order) under distinct variable names, and its model structure, read from the
rendered attributes, lists every output, every state derivative in state order
and every calculated variable as an initial unknown, with no start value on a
calculated variable (FMI 3.0.2 §2.4.7, §2.4.8, Tables 17 and 23). -/
namespace Rumoca.FMI3
open Rumoca.Solve Rumoca.FMI3.DeclaredMetadata

structure InterfaceContract (source : String) (tokens : List _root_.Parser.Token) (i : Interface)
    (root : XML.Element) : Prop where
  /-- The tokens are the lexed source text. -/
  lexed : lex source = .ok tokens
  /-- The declarations are the ones written in the source. -/
  declared : declaredIn tokens = i.declarations.map Declaration.signature
  /-- Every name a declaration reads is declared, so no dependency is dropped. -/
  closed : i.Closed
  /-- The model description exports exactly those declarations. -/
  exported : DeclaredMetadata.exported root = i.declarations.map DeclaredMetadata.Declaration.exported
  /-- Every exported variable name is distinct. -/
  names_unique : (variableNames root).Nodup
  /-- `<Output>` lists exactly the variables rendered with causality `output`. -/
  outputs : (structureOf root "Output").map referenceAttribute =
    ((variablesOf root).filter fun v => v.attributes.lookup "causality" == some "output").map
      referenceAttribute
  /-- `<ContinuousStateDerivative>` lists exactly the derivatives, in state order. -/
  state_derivatives : (structureOf root "ContinuousStateDerivative").map referenceAttribute =
    ((variablesOf root).filter fun v => (v.attributes.lookup "derivative").isSome).map
      referenceAttribute
  /-- `<InitialUnknown>` lists exactly the calculated variables. -/
  initial_unknowns : (structureOf root "InitialUnknown").map referenceAttribute =
    ((variablesOf root).filter fun v => v.attributes.lookup "initial" == some "calculated").map
      referenceAttribute
  /-- A calculated variable carries no start value. -/
  calculated_no_start : ∀ v ∈ variablesOf root,
    v.attributes.lookup "initial" = some "calculated" → v.attributes.lookup "start" = none

/-- Every declared-interface document satisfies the contract for an interface
read back from the lexed source, with distinct declared names and closed
dependencies. -/
theorem interface_correct (source : String) (tokens : List _root_.Parser.Token) (i : Interface)
    (name token : String) (lexed : lex source = .ok tokens)
    (declared : declaredIn tokens = i.declarations.map Declaration.signature)
    (distinct : (i.declarations.map Declaration.name).Nodup) (closed : i.Closed) :
    InterfaceContract source tokens i (DeclaredMetadata.modelDescription name token i) := by
  have words : ∀ d ∈ i.declarations, d.name ≠ timeName ∧ '(' ∉ d.name.toList := fun d member =>
    ((lex_correct source tokens).mp lexed).ident_not_time d.name
      (declaredIn_ident tokens i declared d member)
  exact ⟨lexed, declared, closed, exported_interface name token i, names_nodup name token i distinct words,
    outputs_rendered name token i, stateDerivatives_rendered name token i,
    initialUnknowns_rendered name token i, calculated_no_start name token i⟩

end Rumoca.FMI3
