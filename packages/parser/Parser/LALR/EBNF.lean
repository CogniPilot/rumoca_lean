import Parser.EBNF
import Parser.LALR.Grammar

/-! Context-free desugaring candidates from the existing EBNF reader. Named
references remain nonterminals, including recursive references. Alternatives,
optionals and repetition use fresh helper nonterminals rather than expansion
of the language. The EBNF-to-CFG preservation proof is a separate, open edge;
this frontend is not connected to the production compiler. -/
namespace Parser.LALR.Frontend

private def atoms : EBNF.Expr → List Parser.Symbol
  | .terminal (.literal "") => []
  | .terminal s => [s]
  | .ref _ => []
  | .seq a b | .alt a b => atoms a ++ atoms b
  | .optional a | .many a => atoms a

structure Prepared where
  alphabet : Array Parser.Symbol
  names : Array String
  grammar : Grammar
  deriving Repr

/-- Unknown tokens have their own out-of-range code, distinct from EOF. -/
def Prepared.encode (p : Prepared) (symbol : Parser.Symbol) : Nat :=
  (p.alphabet.findIdx? (· == symbol)).getD (p.alphabet.size + 1)

private structure Builder where
  next : Nat
  productions : Array Production := #[]

private def lowerExpr (alphabet : Array Parser.Symbol) (names : Array String) :
    EBNF.Expr → Builder → Except String (List Atom × Builder)
  | .terminal (.literal ""), b => .ok ([], b)
  | .terminal s, b => do
    let some t := alphabet.findIdx? (· == s) | throw "terminal missing from alphabet"
    return ([.terminal t], b)
  | .ref name, b => do
    let some n := names.findIdx? (· == name) | throw s!"undefined rule {name}"
    return ([.nonterminal n], b)
  | .seq a c, b => do
    let (left, b) ← lowerExpr alphabet names a b
    let (right, b) ← lowerExpr alphabet names c b
    return (left ++ right, b)
  | .alt a c, b => do
    let (left, b) ← lowerExpr alphabet names a b
    let (right, b) ← lowerExpr alphabet names c b
    let n := b.next
    return ([.nonterminal n], ⟨n + 1, b.productions.push ⟨n, left⟩ |>.push ⟨n, right⟩⟩)
  | .optional a, b => do
    let (body, b) ← lowerExpr alphabet names a b
    let n := b.next
    return ([.nonterminal n], ⟨n + 1, b.productions.push ⟨n, []⟩ |>.push ⟨n, body⟩⟩)
  | .many a, b => do
    let (body, b) ← lowerExpr alphabet names a b
    let n := b.next
    return ([.nonterminal n],
      ⟨n + 1, b.productions.push ⟨n, []⟩ |>.push ⟨n, body ++ [.nonterminal n]⟩⟩)

def lower (source : EBNF.Grammar) : Except String Prepared := do
  if source.isEmpty then throw "empty grammar"
  let names := source.map (·.1)
  if names.eraseDups.length != names.length then throw "duplicate rule name"
  let alphabet := (source.flatMap fun (_, e) => atoms e).eraseDups.toArray
  let mut builder : Builder := ⟨source.length, #[]⟩
  for ((_, expr), index) in source.zipIdx do
    let (rhs, next) ← lowerExpr alphabet names.toArray expr builder
    builder := { next with productions := next.productions.push ⟨index, rhs⟩ }
  return ⟨alphabet, names.toArray, ⟨alphabet.size, builder.next, 0, builder.productions⟩⟩

def compile (source : String) : Except String Prepared := do
  lower (← EBNF.parse source)

end Parser.LALR.Frontend
