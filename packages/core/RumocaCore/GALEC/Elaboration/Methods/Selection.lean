import Parser.UniqueSelection
import GALECParser.AST

/-! Exact original-token method selection. No parser, profile body, declaration
policy or method permissions are involved. In particular this does not normalize
literal/identifier spellings or inspect/rebuild the selected method body. -/
namespace Rumoca.GALEC.Elaboration.Methods.Selection
open _root_.Parser

def select (name : Token) (methods : List AST.Method) : Option AST.Method :=
  _root_.Parser.UniqueSelection.select AST.Method.name name methods

abbrev Selects (name : Token) (methods : List AST.Method) (method : AST.Method) : Prop :=
  _root_.Parser.UniqueSelection.Selects AST.Method.name name methods method

theorem select_iff (name : Token) (methods : List AST.Method) (method : AST.Method) :
    select name methods = some method ↔ Selects name methods method :=
  _root_.Parser.UniqueSelection.select_iff AST.Method.name name methods method

/-- Both membership of the untouched method and its complete original token
are retained; no `DecidableEq AST.Method` is required. -/
theorem selected_original (selected : Selects name methods method) :
    method ∈ methods ∧ method.name = name :=
  ⟨selected.mem, selected.key_eq⟩

theorem repeated_rejected (name : Token) (before between after : List AST.Method)
    (a b : AST.Method) (first : a.name = name) (second : b.name = name) :
    select name (before ++ [a] ++ between ++ [b] ++ after) = none :=
  _root_.Parser.UniqueSelection.select_repeated AST.Method.name name before between after a b first second

end Rumoca.GALEC.Elaboration.Methods.Selection
