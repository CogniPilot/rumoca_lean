# Tiny GALEC grammar

`GALEC.ebnf` is an authored restriction of eFMI **1.0.0 Beta 1**, using the
official specification and accompanying schemas as authority. It contains
only the zero-start, unit-period unit integrator's declarations, three methods
and assignments. This demonstrates another EBNF instance of the shared LR
engine without adding any Modelica equation cases.

The file is not copied verbatim from the full standard grammar. In particular,
`do_step` is a rule name in our small EBNF dialect; ISO 14977-style hyphenated
meta-identifiers are not implemented. GALEC comments, quoted names and general
numeric forms remain outside this source profile. The exact-profile scanner
and actions are separate from the EBNF reader and the generic LR engine.

The [standards review](../../../dev/efmi.md) records a Beta 1 discrepancy between
the state-declaration production and its specified input/output interface.
Our `output Real x;` follows the interface rules and examples. Neither grammar
freshness nor parser proofs alone establish full GALEC/eFMI conformance.
