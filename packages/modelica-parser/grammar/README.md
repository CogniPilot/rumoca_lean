# Modelica grammar

`Modelica.ebnf` is a subset of the Modelica Language Specification 3.7
Appendix A syntax, in the ISO comma dialect that `GALEC.ebnf` also uses. Line
numbers below refer to the pinned annex `build/modelica-3.7-syntax-reference.html`.
Every production keeps its annex name and the order of its annex sequence.
Alternatives outside the subset are omitted whole, and optional parts are
deferred to the slice that introduces them; the table lists both. A deferred
optional part is absent from the grammar, so a source that writes it is a syntax
rejection until its slice admits it. Admission of classes, declarations,
equations, operators and callees is static semantics after parsing (see [the
package README](../README.md)); the grammar never encodes a particular model.

| Productions (annex lines) | Present | Not yet present |
| --- | --- | --- |
| `stored-definition` (317-330) | `{ class-definition ";" }` | `within-clause`, `final` |
| `class-definition`, `class-prefixes`, `class-specifier`, `long-class-specifier` (343-404) | `model`; `IDENT composition end IDENT` | `encapsulated`, `partial` and every other class kind, short and der specifiers, `description-string` |
| `composition`, `element-list`, `element` (466-536) | element list, equation sections | `public`/`protected`, algorithm sections, `external`, annotation, import, extends, class elements, element prefixes |
| `component-clause`, `type-prefix`, `type-specifier`, `component-list`, `component-declaration`, `declaration` (653-708) | complete component clause with `input`/`output` | `flow`/`stream`, variability, leading `.` of a type, condition attribute, description |
| `modification` through `element-modification` (718-785) | both modification forms, `each` | `break`, `final`, redeclaration and replaceable elements, description string |
| `equation-section`, `some-equation`, `equation-or-procedure`, `simple-equation` (846-900) | equation sections of simple equations | `initial`, if/for/connect/when equations, procedure calls, description |
| `expression` through `relation` (1171-1229) | the unit chain | if-expressions, ranges, `or`, `and`, `not`, relational operators |
| `arithmetic-expression`, `add-operator`, `term`, `mul-operator`, `factor` (1243-1283) | leading sign, `+ - * / .*` | `.+ .- ./`, `^ .^` |
| `primary` (1288-1320) | references, calls of references and `der`, `false`, `true`, parenthesized output lists | numbers as a separate alternative (see D3), `STRING`, `time`, `initial`/`pure` calls, postfixes, matrix and array constructors, `end` |
| `name`, `component-reference` (1354-1367) | complete | |
| `function-call-args` through `function-argument` (1387-1463) | positional arguments | reductions, named arguments, partial application |
| `output-expression-list`, `array-subscripts`, `subscript` (1477-1508) | complete, expression subscripts | `:` subscripts |

Deviations, each with its certificate:

| ID | Annex form | Grammar form | Reason and certificate |
| --- | --- | --- | --- |
| D1 | `[ add-operator ] term { add-operator term }` | `term, {...} \| add_operator, term, {...}` | A leading optional part before an `IDENT`-initial remainder conflicts under the LALR lowering once named arguments exist; the annex itself sanctions left factoring (1161-1163). `Annex.arithmetic_expression_iff`, an instance of `EBNF.Derives.optional_seq_iff`, proves the word languages equal. |
| D2 | `[ "." ] IDENT [ array-subscripts ] { ... }` | the alternative without and with the leading `.` | The same conflict. `Annex.component_reference_iff`. |
| D3 | `unsigned-number` is a `primary` alternative | a number is a `Token.number` whose grammar symbol is `IDENT` | A separate `IDENT` alternative is a reduce/reduce conflict with `component-reference`; this is the engine and GALEC precedent. The grammar is a superset of the annex here: a number satisfies every `IDENT` position, including class, declaration, reference-part, modification and callee names, so `model 1 ... end 1;` parses. This is a static-semantic check, not a language equivalence: selection reads a number only as a bare, unindexed, undotted reference and rejects it in every name position (`Select.name`; certified `ProfileChecks.numberName_rejected`). |
| D4 | `Real` is a predefined type name | `Real` is `IDENT` | MLS 2.3.3 does not reserve predefined type names, so this matches the annex language; the MLS 4.9 restriction is a static-semantic check, not part of the grammar: selection requires the type `Real` and rejects predefined type names as declared or referenced names (certified `ProfileChecks.predefinedName_rejected`). |

The lexer implements MLS 3.7 A.1 for the ASCII slice by maximal munch:
identifiers and the §2.3.3 keywords, UNSIGNED-INTEGER and UNSIGNED-REAL numbers
(`2.` and `.5` included; a sign is always an operator, so `1-x` is three
lexical units), STRING literals with the S-ESCAPE set (a `STRING` token, not yet
a grammar terminal), `//` and non-nesting `/* */` comments, and the symbols.
Comments are lexemes with their own source ranges; the grammar reads the other
lexemes, and static semantics rejects a commented source until comments are
admitted. `string_maximal` states that a STRING ends at its first unescaped
quote and `comment_not_nested` that a block comment ends at its first `*/`.
Quoted identifiers are not scanned; the lexer rejects them
(`quoted_identifier_rejected`). Number spellings with a point at an edge (`2.`,
`.5`) are lexed but not admitted as rates (certified `trailingPoint_rejected`,
`leadingPoint_rejected`).

Regenerate both checked and runtime tables with `lake run generate`. The full
gate checks freshness and rejects an actual grammar file changed after
generation.
