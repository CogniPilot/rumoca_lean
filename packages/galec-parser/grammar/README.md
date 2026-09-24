# GALEC grammar

`GALEC.ebnf` is an authored subset of the eFMI **1.0.0 Beta 1** Algorithm Code
syntax, using the official specification and accompanying schemas as authority.
It follows §3.2.4 G-2 (block declarations: an optional direction or `constant`,
a primitive type, a name and optional expression-list dimensions after the
name), G-3 (expressions) and the TODO-labelled statement productions
(assignment and bounded `for` loops; in `a:b:c` the middle expression is the
step). `block` is the start symbol. Method names are ordinary names.

The grammar is general; admission is static semantics after parsing. Section
legality of declaration kinds, extent values, types, callees, operators, the
method set, names and literal values are checked by core elaboration, so the
admitted source language does not grow with the grammar. Only `+` and `*` are
binary operators; further operators are additive alternatives.

The dialect writes rule names with underscores; ISO 14977-style hyphenated
meta-identifiers are not implemented. GALEC comments, quoted names, signed
numerals and exponents remain outside the scanner. Numbers are scanned as
`Token.number` on the `IDENT` grammar symbol. `.*` is not a token
(`Syntax.no_pointwise_token`): `.` and `*` scan separately.

The [standards review](../../../dev/efmi.md) records a Beta 1 discrepancy between
the state-declaration production and its specified input/output interface.
Neither grammar freshness nor parser proofs alone establish full GALEC/eFMI
conformance.
