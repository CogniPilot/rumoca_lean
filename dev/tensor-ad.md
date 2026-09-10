# Tensor arrays and automatic differentiation

Authorized 2026-09-10: grow only the small Modelica array/operator subset
needed to express and verify tensor AD, including the `jacobian` built-in.
This supersedes the earlier blanket pause on developing new grammar. It does
not turn a parsed expression or a real-arithmetic derivative rule into a
verified production FMU.

## First language increment

Reuse the relevant productions from
`~/git/rumoca/crates/rumoca-phase-parse/src/modelica.par`: array subscripts on
Real declarations, component references, addition, pointwise multiplication,
parentheses and the argument list for `jacobian(expression, variable)`.
Keep dimensions static and the first source cases to vectors and their
rank-two Jacobians. Do not bring in general functions, loops, indexing, dynamic
dimensions or a broad expression grammar just to support this first case.

The parser records a built-in call and both argument spans. Resolution checks
the differentiated variable; typed lowering determines input and output
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

This is the admission target, not a model accepted by the current compiler.
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
Array and `jacobian` source acceptance, complete AD program transformations
and tensor FMU target certificates are not yet complete. The public EBNF is
still unchanged; syntax will be added with its AST actions and preservation
proofs, rather than enabling unhandled grammar alternatives.
