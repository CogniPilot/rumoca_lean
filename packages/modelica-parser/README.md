# Modelica frontend

This Lake package instantiates the generic [parser engine](../parser/README.md).
It owns the [Modelica EBNF](grammar/Modelica.ebnf), its generated LALR tables,
the Modelica lexical policy, the general syntax tree and its structural actions,
source locations and bounded parsing of independent files. Its modules are
`ModelicaParser.*`; the language API keeps the `Rumoca` namespace.

From the root workspace, inside `nix develop`:

```sh
lake build check-modelica-parser
lake run generate
lake run check-generated
```

The coordinating generation command runs `lalrgen` with explicit language
namespaces. Modelica and GALEC use the same reusable engine, EBNF lowering and
checked input-size bound. Language ASTs never become dependencies of the engine.

`Rumoca.Modelica.parse` lexes once, runs the certified LALR parser once on the
code tokens (every lexeme except comments) and applies the structural actions
of every grammar rule (`StructuralActions`) to that same tree.
`ActionCoverage` proves the actions cover exactly the authored grammar;
`ActionYield` proves every rule's result prints back to the tokens it was parsed
from, so `Structural.parse_printed` binds the syntax tree to the lexed
characters. `StructuralParser.accepts_iff` states the accepted language
for all token sequences. `Annex` proves that the two left-factored productions
denote the words of their MLS 3.7 Appendix A forms.

The grammar accepts more than any admitted model. Admission is static
semantics in the core package (`RumocaCore.Modelica`): a selection reads a
record from the parsed tree or rejects it at an offending token, and proves
that a selected tree prints to its record's tokens. `Invariant` proves that
every parsed tree keeps each retained token in its grammar class
(`Good.parse_good`), `Inversion` reads such a tree back from its printed
tokens, and `Derivations` derives the admitted forms in the EBNF language;
together they give each selection its completeness theorem.

`Certificate.certify_source` kernel-checks the parse of a concrete source text:
the lexer result, the accepted tree, the structural value and the typed action
result are separate reflexivity or constructor proofs, and the LR parser is not
evaluated in the kernel. Actual-artifact checkers use it to bind their source
file to the compiled record. `certify_family` certifies the same way, for all
values of string parameters, the parse of a token family whose grammar symbols
do not depend on them.

`LocatedParser` attaches exact UTF-8 ranges to the same lexed tokens; a syntax
rejection is reported at the first token the certified parser could not accept.
`LocatedCompleteness` proves that attachment succeeds for every lexed source.
`Parallel` parses independent files with a sequential-equivalence theorem.

The optional `modelica_parser/frontend-bench` executable measures the
read/lex/parse/located stages without importing artifact backends. Run it through
`lake run benchmark-frontend`; raw measurements stay under `build/` and are
independent of the proof gate. `lalr-tests` executes the generated tables
natively on the lexed example sources. See the [grammar
restrictions](grammar/README.md) and the [verification
boundary](../../docs/verification.md).
