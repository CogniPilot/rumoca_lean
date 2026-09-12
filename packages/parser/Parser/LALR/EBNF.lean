import Parser.EBNF.ReaderCorrectness
import Parser.LALR.EBNFEncoding

/-! Certified context-free desugaring from the EBNF reader's expression tree.
Sequences remain inline and references remain nonterminals, including recursive
references. Alternatives, optionals and repetition use fresh helpers. Candidate
construction must pass the independent finite structural witness checker before
its grammar is returned. The public text-to-CFG theorem composes independent
notation syntax with expression-to-CFG language preservation. -/
namespace Parser.LALR.Frontend

private def atoms : EBNF.Expr → List Parser.Symbol
  | .terminal (.literal "") => []
  | .terminal s => [s]
  | .ref _ => []
  | .seq a b | .alt a b => atoms a ++ atoms b
  | .optional a | .many a => atoms a

private structure Builder where
  meanings : Meanings
  rules : Array AnnotatedRule := #[]

private def lowerExpr (alphabet : Array Parser.Symbol) (names : Array String) :
    EBNF.Expr → Builder → Except String (Fragment × Builder)
  | .terminal (.literal ""), b => .ok (.empty, b)
  | .terminal s, b => do
    let some t := alphabet.findIdx? (· == s) | throw "terminal missing from alphabet"
    return (.terminal s t, b)
  | .ref name, b => do
    let some n := names.findIdx? (· == name) | throw s!"undefined rule {name}"
    return (.ref name n, b)
  | .seq a c, b => do
    let (left, b) ← lowerExpr alphabet names a b
    let (right, b) ← lowerExpr alphabet names c b
    return (.seq left right, b)
  | .alt a c, b => do
    let (left, b) ← lowerExpr alphabet names a b
    let (right, b) ← lowerExpr alphabet names c b
    let n := b.meanings.size
    return (.alt n left right,
      ⟨b.meanings.push (.alt a c), b.rules.push (.altLeft n left right) |>.push (.altRight n left right)⟩)
  | .optional a, b => do
    let (body, b) ← lowerExpr alphabet names a b
    let n := b.meanings.size
    return (.optional n body,
      ⟨b.meanings.push (.optional a), b.rules.push (.optionalEmpty n body) |>.push (.optionalSome n body)⟩)
  | .many a, b => do
    let (body, b) ← lowerExpr alphabet names a b
    let n := b.meanings.size
    return (.many n body,
      ⟨b.meanings.push (.many a), b.rules.push (.manyEmpty n body) |>.push (.manyCons n body)⟩)

private def candidate (source : EBNF.Grammar) : Except String (Prepared × Witness) := do
  if source.isEmpty then throw "empty grammar"
  let names := source.map (·.1)
  if names.eraseDups.length != names.length then throw "duplicate rule name"
  let alphabet := (source.flatMap fun (_, e) => atoms e).eraseDups.toArray
  let mut builder : Builder := ⟨(names.map EBNF.Expr.ref).toArray, #[]⟩
  let mut roots : Array Fragment := #[]
  for ((name, expr), index) in source.zipIdx do
    let (fragment, next) ← lowerExpr alphabet names.toArray expr builder
    builder := { next with rules := next.rules.push (.named index name fragment) }
    roots := roots.push fragment
  let grammar : Grammar := ⟨alphabet.size, builder.meanings.size, 0,
    builder.rules.map AnnotatedRule.production⟩
  return (⟨alphabet, names.toArray, grammar⟩, ⟨builder.meanings, roots, builder.rules⟩)

/-- Proof fields erase during execution; emitted witness constants are checked
again by Lean's kernel before they can justify a generated parser. -/
structure Certified (source : EBNF.Grammar) where
  prepared : Prepared
  witness : Witness
  wellFormed : prepared.grammar.wellFormed = true
  checked : witness.Conditions source prepared

def lowerWithWitness (source : EBNF.Grammar) : Except String (Certified source) := do
  let (prepared, witness) ← candidate source
  if wf : prepared.grammar.wellFormed = true then
    if valid : witness.validate source prepared = true then
      return ⟨prepared, witness, wf, Witness.validate_iff.mp valid⟩
    else throw "candidate failed EBNF language-preservation validation"
  else throw "candidate CFG is not well formed"

def lower (source : EBNF.Grammar) : Except String Prepared := do
  return (← lowerWithWitness source).prepared

def compile (source : String) : Except String Prepared := do
  lower (← EBNF.parse source)

/-- Reuse an already checked reader result instead of repeatedly reducing
source text during later lowering certificates. -/
theorem compile_of_parse (read : EBNF.parse text = .ok source) :
    compile text = lower source := by
  unfold compile
  rw [read]
  rfl

theorem Certified.accepts_iff (certificate : Certified source) (word : List Parser.Symbol) :
    EBNF.Accepts source word ↔
      certificate.prepared.grammar.Accepts (word.map certificate.prepared.encode) :=
  certificate.witness.accepts_iff certificate.checked certificate.wellFormed word

/-- The public desugaring function only returns language-preserving grammars. -/
theorem lower_correct (result : lower source = .ok prepared) (word : List Parser.Symbol) :
    EBNF.Accepts source word ↔ prepared.grammar.Accepts (word.map prepared.encode) := by
  unfold lower at result
  cases h : lowerWithWitness source with
  | error error => simp only [h] at result; contradiction
  | ok certificate =>
    rw [h] at result
    cases Except.ok.inj result
    exact certificate.accepts_iff word

/-- The actual text-to-CFG entry preserves the language of the independently
denoted EBNF grammar. Candidate validation may still reject unsupported inputs. -/
theorem compile_correct (result : compile text = .ok prepared) :
    ∃ source, EBNF.Metalanguage.Denotes text source ∧
      ∀ word, EBNF.Accepts source word ↔ prepared.grammar.Accepts (word.map prepared.encode) := by
  unfold compile at result
  cases h : EBNF.parse text with
  | error error => simp only [h] at result; contradiction
  | ok source =>
    rw [h] at result
    exact ⟨source, EBNF.parse_sound h, lower_correct result⟩

end Parser.LALR.Frontend
