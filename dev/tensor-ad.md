# Tensor arrays and automatic differentiation

Authorized 2026-09-10: grow only the small Modelica array/operator subset
needed to express and verify tensor AD, including the `jacobian` built-in.
This supersedes the earlier blanket pause on developing new grammar. It does
not turn a parsed expression or a real-arithmetic derivative rule into a
verified production FMU.

## First language increment

Reuse the relevant productions from
`~/git/rumoca/crates/rumoca-phase-parse/src/modelica.par`: array subscripts on
Real declarations, component references, pointwise multiplication,
and the argument list for `jacobian(expression, variable)`.
Keep dimensions static and the first source cases to vectors and their
rank-two Jacobians. Do not bring in general functions, loops, indexing, dynamic
dimensions or a broad expression grammar just to support this first case.

The parser records an ordinary call and both argument spans. Resolution selects
the built-in and checks the differentiated variable; typed lowering determines input and output
shapes. The first nonlinear rule is pointwise multiplication, allowing
`jacobian(x .* x, x)`. The result for an n-vector is an n-by-n tensor. It must
not become n separate source equations or an unrolled n-by-n instruction list.

The first intended source model is deliberately only two-wide. Its formal
operator rules remain general in the shape:

```modelica
model TensorSquare
  input Real u[2];
  output Real x[2](each start=0, each fixed=true);
  output Real J[2,2];
equation
  der(x) = u .* u;
  J = jacobian(u .* u, u);
end TensorSquare;
```

This is accepted by the development array parser, and is the production
admission target. The current production compiler rejects it.
The array input/state baseline precedes the nonlinear and Jacobian equations;
source `+` is unnecessary until a model requires it, even though AD needs
addition internally to accumulate cotangents.

Rust SPEC_0051 recognizes the narrower `jacobian(f(a, b), a)` form after parsing
ordinary call syntax, and currently emits Modelica tangent functions with
unrolled Jacobian seeds. The Lean implementation will share the intrinsic
interface but support the direct expression first and derive tensor programs
inside the typed IR. This avoids adding function definitions or copying the
seed-unrolling design. The exact extension is documented separately from
standard Modelica syntax.

## Proof and execution obligations

1. Define the shape-indexed operator and its array-backed evaluator. Prove its
   denotation at every coordinate, including empty tensors, without a per-size
   compiler expansion.
2. Prove the forward rule with mathlib `HasFDerivAt`, and the reverse rule by
   the dual pairing with that same derivative. These are derivatives of the
   mathematical Real operator; IEEE rounding is a separate target contract.
3. Implement forward and reverse transformations of the typed tensor program.
   Prove primal preservation, chain composition and accumulation when operands
   share a register. Reverse execution must retain forward intermediates rather
   than repeatedly evaluating subgraphs.
4. Give `jacobian` a matrix denotation connected to those operators. JVP and
   VJP remain directly executable without first constructing the matrix;
   explicit Jacobian outputs materialize only at a consumer that needs them.
5. Extend the generated grammar, located AST, Flat, DAE and Solve one source
   case at a time, with adjacent preservation theorems and refusal of unsupported
   cases. Use one nonlinear array model and an input/state baseline.
6. Lower these prepared tensor programs in the shared backend. Prove ordered
   finite arithmetic, loop/storage behavior and FMI aggregate dimensions/value
   references; bind the actual FMU and eFMU products to those contracts.

The initial primitive set is addition and pointwise multiplication. Matrix
contraction, sparsity analysis, coloring, higher derivatives and new solver
policies are later increments, each with its own proof. The matrix-free
forward/reverse distinction follows the
[CasADi calculus interface](https://web.casadi.org/docs/#calculus-algorithmic-differentiation).

Current implementation: `Tensor.Operators` provides dense-array addition,
pointwise multiplication and JVP/VJP rules with an explicit scalar arithmetic
interface. `Tensor.Differentiation` proves those rules for arbitrary shapes
using mathlib's Fréchet derivative and finite dot-product pairing. It also
proves the derivative, accumulated pullback and diagonal Jacobian of `x .* x`.
`lake build check-core` passed in `build/tensor-ad-package.log` with eight new
audited roots and no additional example tests. All roots use only the existing
three permitted foundational axioms.
The generated EBNF now also recognizes the two-wide driven and square/Jacobian
profiles. `ModelicaParser.Array` supplies structured product/call syntax,
decoder soundness/completeness, recognition proofs and name resolution.
The lexer treats `.*` atomically and `jacobian` as an identifier; its universal
soundness/completeness theorem covers the extension. `ActionsLocated` reuses
the checked lexer alignment for any semantic action profile; `callLocation`
binds each call-name/operand range to that AST field's source text and proves
the full call range contains both arguments. The parser package audit passed
in `build/tensor-parser-audit.log`, with no new axioms.

`RumocaCore.Array.Builtin` specifies the parsed intrinsic using a true
`HasFDerivAt` witness and equality of its action on every tangent to matrix
multiplication. All other named values stay fixed while the selected variable
changes. The matrix is proved unique; `Model.jacobian_call_correct` connects
the resolved AST to the diagonal square Jacobian for arbitrary shapes. The
three added roots pass the core audit in `build/tensor-builtin-audit.log`.

Use `Rumoca.ArrayProfile.parseLocated` from `ModelicaParser.Array.Located` for
the development frontend. It preserves other callee names for structured
resolution errors; it does not silently interpret every call as a Jacobian.
The production CLI/LSP still select the unit frontend. Array source-to-IR
lowering, static reverse transformation and finite tensor FMU/eFMU target
certificates remain open. Parser acceptance does not authorize production
generation.

The required `nix develop .#verification --command lake test` passed for the
array/frontend and intrinsic-semantics increment in
`build/tensor-parser-full-gate.log`, including the actual C, FMU and eFMU
contracts and their rejection checks. This revalidates the production unit
profile; it does not certify tensor FMUs. A subsequent LALR certificate-emission
refactor reduces proof-checking memory while preserving the same validator;
its evidence is tracked in [the parser roadmap](lalr-parser.md).

## Whole-program AD checkpoint

`Solve.Tensor.Program` includes one typed binary instruction for pointwise
addition or multiplication. Its evaluator and independent denotation agree
for every program and arbitrary explicit scalar arithmetic. IVP evaluation
takes that arithmetic explicitly; the existing unit/driven contracts remain
checked. No backend performs this work and no source syntax was added here.

| Obligation | Checked theorem |
| --- | --- |
| Dense array program implements its denotation | `Program.eval_correct` |
| Forward transformation preserves its ordered operations | `Program.forward_correct` |
| Forward transformation preserves primal output | `Program.forward_primal` |
| At most four target instructions per source instruction, regardless of extents | `Program.forward_compact` |
| Whole-program chain rule, allowing shared input dependencies | `Program.hasFDerivAt` |
| Emitted forward program computes the mathematical derivative | `Program.forward_derivative` |
| Reverse evaluation preserves primal output | `Program.reverse_primal` |
| Every accumulated contribution is retained, without assuming distinct operands | `Env.pair_addAt` |
| Reverse execution is the adjoint of forward execution | `Program.reverse_pairing` |
| Reverse execution pairs with the mathematical derivative | `Program.reverse_derivative` |

The twelve added audit roots pass in `build/tensor-program-audit.log`. The
existing native integration executable has one additional smoke check for
`(u .* u + 1)^2` on a tensor: primal execution, emitted JVP and saved VJP agree
with their expected results (`build/tensor-program-native.log`). The program
uses repeated nonlinear intermediates, literals and addition; it does not
add that expression to the source grammar.

Forward AD emits ordinary Solve instructions. Reverse execution currently
builds a pullback closure over saved forward values. It does not re-evaluate
the primal program when a cotangent is supplied, but it is not yet a static
Solve-to-Solve reverse transformation suitable for C emission. Neither path
constructs a full Jacobian to compute a directional product.

The instruction bound is not a runtime complexity theorem. The reference
environment uses dependent functions and references; lookup/update cost can
grow with register depth. A packed register store needs a simulation theorem
before replacing this evaluator. No claim of CasADi-level performance is made.

Next, close the array AST → Flat → DAE → Solve equations, initialization and
Jacobian-output contracts at the fixed declared shapes. Preserve one whole
tensor operation in each stage and keep production rejection until the
ordered finite arithmetic, shared C loops and actual FMU/eFMU contracts pass.
