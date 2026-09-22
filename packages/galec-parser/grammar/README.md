# Tiny GALEC grammar

`GALEC.ebnf` is an authored restriction of eFMI **1.0.0 Beta 1**, using the
official specification and accompanying schemas as authority. It contains
the zero-start, unit-period scalar integrator and fixed extent-two tensor
square/Jacobian profile. Both use the shared LALR engine and typed structural
actions, without adding Modelica equation cases. Tensor declarations place
dimensions after the name, as required by Beta 1 §3.2.4 G-2; the old
type/dimensions/name spelling is rejected. The ordinary call named `jacobian`
still has the separate GJ01 definition/interface finding.

The file is not copied verbatim from the full standard grammar. In particular,
`do_step` is a rule name in our small EBNF dialect; ISO 14977-style hyphenated
meta-identifiers are not implemented. GALEC comments, quoted names and general
numeric forms remain outside this source profile. The exact-profile scanner
and actions are separate from the EBNF reader and the generic LR engine.

The [standards review](../../../dev/efmi.md) records a Beta 1 discrepancy between
the state-declaration production and its specified input/output interface.
Our `output Real x;` follows the interface rules and examples. Neither grammar
freshness nor parser proofs alone establish full GALEC/eFMI conformance.
