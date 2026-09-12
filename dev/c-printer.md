# Reusable C printer verification

This work closes shared proof prerequisites for the existing adapter code. It
adds no Modelica or GALEC production and changes no emitted C bytes. The whole
compiler and FMI/eFMI conformance contracts remain open.

The numerical and tensor printers already connect their emitted fragments to
independent C grammars. The FMI reset certificate also covers a complete
function, but its syntax relation spells out that particular function. Further
adapter functions should instantiate shared syntax and printer theorems.

## Current increment

`Parser.Scanner.Prefix` gives compositional scanning judgments with the actual
remaining characters present. Composition preserves word/number maximal munch
and configured symbol boundaries. Complete prefixes agree with the existing
scanner relation. This adds a proof interface, not an executable C parser.
Its six new audit roots pass `build/source-cutover/build/c-printer/parser-audit.log` in the isolated
checkout (792 jobs).

`RumocaC.TreePreprocessing` proves stability under trigraph replacement and
physical newline splicing. Its `Stable` fragments compose without creating a
rewrite across a boundary. Arbitrary UTF-8 string payloads reuse the existing
`CString` escaping and literal proofs. The theorem covers every CTree
expression and statement constructor, parameter lists, signatures and complete
functions. Raw names and type strings must contain no question marks or
backslashes. This condition is weaker than lexical or typing validity.

The complete module and its 19 new roots pass the unchanged C package axiom
audit in `build/source-cutover/build/c-printer/c-audit-v1.log` (2161 jobs). `RuntimePreprocessing`
discharges the body precondition for every branch of the actual FMI emitter.
`AdapterPreprocessing` composes helpers, declarations, prefixes and public
functions into the complete `Runtime.render` result. The FMI package audit
passes in `build/source-cutover/build/c-printer/adapter-audit.log` (1211 jobs). Those package passes
cover 33 new roots across the parser and C/FMI packages.

The next composition strengthens `AdapterContract` with stability of the actual
file characters. Model-name safety follows from the existing parsed-name theorem;
signature spellings are checked using standard-library decidability in the
kernel certificate. A public consequence exposes the new file guarantee.
That composition and its two added roots pass the affected-package audit in
`build/source-cutover/build/c-printer/composed-package-audit.log` (2442 jobs).
The fixed `CheckFMI3Build.lean` passed on files extracted from the retained FMU
in `build/source-cutover/build/c-printer/actual-fmi.log`. All 35 added roots
retain the unchanged axiom policy. The required main artifact gate passed in
`build/c-printer/full-gate.log`, including both actual archives and the existing
native/mutation boundaries. All 596 inventoried inputs remained unchanged.
The exact archives and hashes are retained in `build/c-printer/artifacts/`.

## Standards correspondence and remaining work

The primary C reference is [WG14 N1570](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf).
Sections 5.1.1.2 and 5.2.1.1 describe the character rewrites modeled here.
Source/execution encodings, preprocessing directives and header meanings are
separate obligations; character stability does not establish them.

- [x] Complete the required artifact gate for the shared character theorem's
  binding to the actual adapter, prefixes and declarations. The strengthened
  actual-file contract, package audits and full gate pass as recorded above.
- [ ] Define a reusable independent token grammar for the existing C tree.
  Review longest preprocessing-token matching (§6.4p4), encoding prefixes and
  adjacent string concatenation (§6.4.5), all relevant longer punctuators
  (§6.4.6) and preprocessing numbers (§6.4.8). The current restricted scanner
  configuration alone does not establish full C tokenization.
- [ ] Prove each admissible CTree renders into that grammar. Express raw type
  spellings and typedef contexts explicitly. Keep scope, type and object/call
  validity separate from mere syntactic acceptance.
- [ ] Replace function-specific printer premises with the generic theorem,
  preserving every existing numerical, memory, call and actual-byte contract.
- [ ] Complete the public adapter call proofs and compose the actual artifacts.
  Allocation, callbacks, lifecycle error behavior and header/ABI assumptions
  must retain their own reviewed contracts.

These steps are prerequisites for the existing frozen grammar's assurance
closure, not permission to grow the source language.
