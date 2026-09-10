# Tiny Modelica frontend

This Lake package instantiates the generic [parser engine](../parser/README.md).
It owns the selected [Modelica EBNF](grammar/Modelica.ebnf), generated DFA tables,
Modelica lexical policy, AST and actions, resolution, source locations and
bounded parsing of independent files. The semantic API remains in `Rumoca`;
its implementation modules are `ModelicaParser.*`.

From the root workspace, inside `nix develop`:

```sh
lake build check-modelica-parser
lake run generate
lake run check-generated
```

The coordinating generation command runs the engine's EBNF tools with explicit
language namespaces. Generated and runtime tables remain connected by the
existing kernel-checked equality and grammar-preservation proofs. Language
ASTs and resolution never become dependencies of the engine.

The production unit profile still uses the certified DFA. The development
LALR executable also exercises this EBNF; the split does not switch the production
parser algorithm or expand the accepted language. See the [grammar restrictions](grammar/README.md)
and [verification boundary](../../docs/verification.md).

`ModelicaParserChecks` audits the source lexer, grammar, AST actions and parser
contracts, exact identifier spans and sequential/parallel equivalence.
