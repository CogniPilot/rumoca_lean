# Design references and deliberate reductions

Modelica states the system's equations and constraints. The Lean compiler
elaborates and lowers that specification into an explicit Solve IR computation,
and Lean proofs relate the computation to the original mathematical problem.
Solver construction and numerical policy belong to the compiler/solver layers;
they are not inferred merely by treating Modelica as an imperative program.

Lean can express both implicit mathematical relations and executable algorithms.
The useful distinction is between specifying a system and constructing a
verified computation for it. For a numerical solver, the connection may be a
refinement with an error bound under explicit assumptions, rather than equality
to an exact continuous solution. The existing tiny profile is a first checked
instance of this design, not an automatic solver for arbitrary DAEs.

The implementation is new Lean code. The contracts come from the
[Rumoca `msl-trace-parity-50` specs](https://github.com/CogniPilot/rumoca/tree/msl-trace-parity-50/spec).
The neighboring reference checkout was on that branch at
`a1daf47556c1a6ffd7f4b203235ff09711089a85` when inspected. No files in that
checkout were changed.

The subsequent [IR alignment review](../dev/ir-review.md) compares actual Rust
definitions with the small Lean types. Shared tensor shape/storage, a mathlib
matrix view, explicit initialization residuals and a correlated Solve export
root are being added for the minimal driven profile. This does not expand the
current production source-to-C theorem or implement an FMI archive.

| Reference | Retained idea | Tiny Lean implementation |
| --- | --- | --- |
| [SPEC_0031](https://github.com/CogniPilot/rumoca/blob/msl-trace-parity-50/spec/SPEC_0031_COMPILER_PHILOSOPHY.md) | Portable symbolic systems; separate solver policy | DAE and Solve have no target word size or sample count; the host is separate |
| [SPEC_0007](https://github.com/CogniPilot/rumoca/blob/msl-trace-parity-50/spec/SPEC_0007_IR_PIPELINE.md) | AST → Flat → DAE → Solve | Distinct types and separate semantics at each edge |
| [SPEC_0036](https://github.com/CogniPilot/rumoca/blob/msl-trace-parity-50/spec/SPEC_0036_VALID_BY_CONSTRUCTION_IR.md) | Invalid IR unrepresentable | Source-indexed products, `Fin 1` state references, register-count-indexed programs, equality proofs |
| [SPEC_0037](https://github.com/CogniPilot/rumoca/blob/msl-trace-parity-50/spec/SPEC_0037_FORMALLY_VERIFIED_COMPILER.md) | Small checked relations; name numerical and trust boundaries | Generic table certificate, layer theorems, binary64 semantics, axiom audit |
| [SPEC_0040](https://github.com/CogniPilot/rumoca/blob/msl-trace-parity-50/spec/SPEC_0040_IR_STAGE_CONTRACT_CATALOG.md) | Explicit derivative coordinates; scalar constant-derivative refinement | `der(state)` lowers to a derivative coordinate, then the unique unit RHS |

Rust ownership brands, mutable arenas, compatibility layers, serialization
formats, optimizer infrastructure, and the wider feature catalogs are not
ported. Lean propositions bind the exact source and output values directly.
This does not implement Rumoca's FMI contract or the full C61 profile (including
fixed starts); those are separate future milestones.

## Modelica 3.7 mapping

The reference is specifically [MLS 3.7](https://specification.modelica.org/maint/3.7/MLS.html).

| MLS section | This core |
| --- | --- |
| [§2 lexical structure](https://specification.modelica.org/maint/3.7/lexical-structure.html) | ASCII unquoted identifiers, reserved words, decimal digit tokens, four whitespace characters; comments and quoted identifiers rejected |
| [Appendix A grammar](https://specification.modelica.org/maint/3.7/modelica-concrete-syntax.html) | One long model class, one Real component, one equation, matching end name |
| [§3.7.4 `der`](https://specification.modelica.org/maint/3.7/operators-and-expressions.html#der) | Time derivative of the sole continuous Real state |
| [§8.6 initialization](https://specification.modelica.org/maint/3.7/equations.html#initialization-initial-equation-and-initial-algorithm) | No source initial value is invented; the separate host supplies one |
| [Appendix B](https://specification.modelica.org/maint/3.7/modelica-dae-representation.html) | Continuous residual `dx - 1 = 0` |

The source state is interpreted over mathematical reals. The target stores
finite IEEE754 binary64 values in C `double`, consistent with MLS §4.9.1's Real
mapping. It supports fractional and negative initial values supplied by the
host, and nearest-even rounding at each unit-time increment. The binary64
proof relates those samples to the ideal trajectory; other sample grids
remain outside this milestone.

## Reuse survey

The survey found no ready-to-use verified EBNF-file-to-Lean generator matching
this task. This is a search result, not a claim that none exists.

* [mathlib regular expressions](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/RegularExpressions.html)
  already supplies the language semantics, Brzozowski derivative, alphabet
  mapping, and recognition theorem. These are reused directly, together with
  mathlib real analysis. The initial duplicate regex foundation was removed.
* [fgdorais/lean4-parser](https://github.com/fgdorais/lean4-parser) is a reusable
  parser-combinator library, not an EBNF generator with the required language
  correctness certificate. Its main branch used Lean 4.34.0-rc2 at inspection.
* Lean's built-in `Std.Internal.Parsec` provides useful combinators, but its
  repetition combinators are partial definitions. The small total EBNF reader
  here remains kernel-reducible, allowing the generated source certificate to
  compute its result inside the kernel.
* [Trust-Lean](https://github.com/lambdaclass/trust-lean) provides a broader
  verified integer DSL/C framework and is worth revisiting for a larger target
  language. It pins Lean/mathlib 4.26.0 and was not imported for this three-node
  C expression core. Its README's broader verification claims were not adopted
  as evidence for this project.
* [parol](https://github.com/jsinger67/parol) inspires the separate grammar file,
  preprocessing, and separate semantic actions. Production still uses a regular
  grammar and certified DFA. The new in-tree Lean LALR(1) implementation is a
  development replacement, with general checked-tree soundness and structural
  table safety. Completeness, parsing bounds and EBNF/AST certification remain
  open; see [the parser plan](../dev/lalr-parser.md).
* [CompCert](https://compcert.org/man/manual001.html) inspires composing pass
  semantics and proving all-execution properties. It is a reference only. The
  target grammar and operational semantics are authored in Lean; their
  correspondence to C remains a specification review boundary.
* [FloatSpec](https://github.com/Beneficial-AI-Foundation/FloatSpec), a Lean
  port of Flocq, was inspected for reuse. The needed rounding modules contained
  unfinished proofs and a private tie-uniqueness axiom at inspection, so they
  were not imported. [LeanCert](https://github.com/alerad/leancert) supplies
  verified dyadic interval arithmetic, rather than a drop-in binary64 C
  operation model. This core reuses mathlib's finite minimization, integers
  and real analysis to specify finite binary64 nearest-even rounding.

## Growing the core

Expansion is gated by the tiny all-Lean source-to-C contract and
`nix develop .#verification --command lake test`. Each later case must extend
the source semantics, lowering proof, actual C execution proof, artifact
certificate, and counterexample tests together. Any further floating-point
operation needs its own rounding and error/refinement theorem. Runtime
numerical integration remains separate from symbolic compilation.

The reference's target products were also inspected: `target.toml`, directory
layouts and manifests package FMI 2/3 FMUs and eFMI artifacts. In particular,
eFMI uses correlated AlgorithmCode and ProductionCode products; it is not just
a C template. SPEC_0034 and SPEC_0048 were marked DRAFT. These are design notes
for later work only: no packaging or backend framework is introduced here.
