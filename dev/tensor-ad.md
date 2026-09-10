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
The production CLI/LSP still select the unit frontend. Array source-to-Solve
lowering is now checked as described below. Static reverse transformation and
finite tensor FMU/eFMU target certificates remain open. Parser acceptance does not authorize production
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

The full gate passed locally in `build/tensor-program-full-gate.log` and in
[CI for 8e20731](https://github.com/CogniPilot/rumoca_lean/actions/runs/34459149967).
This includes the production unit profile's actual C/FMU/eFMU checks.

## Array source-to-Solve checkpoint

`Array.IR` retains rank and extents through named source, Flat expressions and
DAE residuals. Resolution fixes operand roles. The DAE still specifies an
implicit derivative residual and an independent mathematical derivative for
the Jacobian equation; it contains no candidate matrix formula.

`Array.Solve` implements a partial residual solver. It accepts the driven and
square residuals, fixed-zero initialization and the optional square Jacobian.
Soundness holds for every successful candidate; completeness is proved for
every source-indexed DAE in this development profile. The total wrapper uses
that completeness proof to eliminate its impossible rejection branch.

The resulting `Solve.PointwiseIVP` stores executable programs for initialization
and the RHS, observes the state directly, and optionally stores a prepared
`DiagonalProgram`. Forward AD generates its coefficients. Mathlib's diagonal
matrix and the existing proved storage bridge materialize the explicit dense
output. The square Jacobian has eight program nodes regardless of extents;
lowering never enumerates tensor elements. This terminal observation is not a
new arithmetic constructor, and no higher-derivative contract is claimed for it.

| Obligation | Checked theorem |
| --- | --- |
| Named source equations and initialization → Flat | `ArrayProfile.Flat.lower_correct`, `lower_initial` |
| Flat → residual DAE | `ArrayProfile.DAE.lower_correct`, `lower_initial` |
| Successful residual/init/Jacobian solving → actual programs | `DAE.solveResidual_correct`, `solveInitial_correct`, `solveJacobian_correct` |
| Every admitted DAE produces an executable kernel | `Solved.lower_complete`, `lower_checked` |
| Complete DAE equations and initialization → actual Solve execution | `Solved.lower_correct`, `lower_initial` |
| Actual dense AD output is the square's mathematical Jacobian | `ArrayProfile.square_jacobian_eval` |
| Complete named AST → executable Solve chain | `ArrayProfile.lowering_chain_correct`, `initialization_chain_correct` |
| Original source parse, EBNF membership and stored kernel contract | `ArrayCompiler.prepare_correct` |

The 19 new core roots and four compiler roots pass the unchanged axiom audit
in `build/array-compiler-audit.log`. The two existing array fixtures now live in
`examples/development/`; the native integration executable prepares them from
their actual file contents and checks initialization, derivatives, state output
and dense Jacobian storage. The universal mathematical theorems, rather than
these examples, establish the Real contract.

The full gate passed locally in `build/array-source-full-gate.log` and in
[CI for c4c4286](https://github.com/CogniPilot/rumoca_lean/actions/runs/34462561010),
including the unchanged production unit C/FMU/eFMU artifacts and rejection
checks. It does not certify production generation for the array examples.

## Finite arithmetic and tensor execution

`Real.ScaledRounding` rounds exact rational inputs on the existing binary64
grid. A product with integer significand units `a` and `b` compares the complete
integer `a*b` with each candidate's units multiplied by `2^1074`. No division
discards bits before the final nearest/even choice. Mathlib supplies finite
minimization and the arithmetic proofs; its opaque witness is proof-only.
Denominator one agrees with the original integer-input rounding operation.

`Real.Multiplication` proves a unique nearest/even product with the operand-sign
XOR for zero results. This includes negative nonzero products that underflow.
The integer overflow guard is equivalent to the strict Real threshold interval.
The guarded operation accepts exactly the independent product relation, with
exactness and half-spacing error bounds. `Real.Addition` proves the corresponding
nearest-value result for the existing addition primitive.
The signed-zero rule was reviewed against the
[Oracle numerical guide](https://docs.oracle.com/cd/E19059-01/stud.9/817-6702/ncg_goldberg.html).
[SoftFloat's documentation](https://www.jhauser.us/arithmetic/SoftFloat-3/doc/SoftFloat.html)
is a reference for rounding/underflow behavior, not a dependency or proof
assumption. Floating-point flags, traps and nonfinite inputs remain outside
this authored finite numerical model.

`Solve.Tensor.Finite.Executes` is an independent inductive execution relation.
Each binary instruction requires its scalar rounding relation at every tensor
coordinate before execution continues. `executes_iff` proves that execution
exists exactly when all instructions are in domain, and equals the actual
array evaluator with binary64 operations. Shared registers, empty tensors and
unused intermediate instructions are included. There is no source-coordinate
enumeration in lowering and no assumption of native Float correctness.

`Array.Finite.square_finite_correct` connects the actual square program to the
product relation at every coordinate; `square_finite_nearest` bounds its result
against the mathematical source RHS. The two Jacobian coefficient theorems
retain the actual ordered `u*1 + u*1` computation and show it is nearest to the
Real derivative `2*u`. The forward program also computes primal intermediates;
their overflow obligations are retained even when only the tangent is returned.
Dense diagonal storage still uses the earlier general materialization theorem.

All 26 added arithmetic/program/array roots pass the unchanged axiom audit in
`build/finite-array-audit.log`. No new example tests were added. Numerical and
program roots live in the independently cached `Tests.FiniteChecks`; the four
array corollaries live in `Tests.TensorChecks`.

This checkpoint also passed
[CI for 1413110](https://github.com/CogniPilot/rumoca_lean/actions/runs/34465555340).

## Counted production C helpers

`CTensor.function` emits one loop for each pointwise add/multiply operation,
independent of shape and extent. `CLoops` retains declared local types and
models the unsigned counter update; `loop_reaches` proves complete execution
from initialization through every iteration and exit. The generated body has
no nested declarations, so its flattened control flow does not lose C scope.

`CMemory.TensorView` represents input/output buffers over the existing typed
symbolic cells. `written_at` proves the initialized prefix invariant;
`store_next` executes each actual typed write; `written_frame` preserves every
cell outside the output range. Inputs may alias one another, which is needed
for `u .* u`. The output range must be separate from both inputs. These
invariants include zero-volume tensors and initially uninitialized outputs.

`CTensor.function_correct` proves that every body behavior terminates with
the finite Solve result. Its premises require valid storage, finite operands,
all coordinate operations in domain, and a count below `2^64` for the authored
`size_t` profile. It neither assumes the loop body implements an operation nor
substitutes a tensor operation for the actual C writes and counter steps.

`TensorSyntax` independently spells out the C tokens for the parameters,
declaration, loop, indexed operation, increment and return. `render_denotes`
checks the structured emitter against the shared scanner's maximal-munch
relation; `denotes_unique` ensures the text cannot denote another operator.
`artifact_correct` composes this with all body behaviors, the independent
`Finite.Pointwise` relation, output reads and the complete memory frame.
The fixed file adapter reads the entire actual helper file, constructs that
contract for its literal contents and audits the exact theorem. Eleven new
roots pass `build/c-tensor-audit.log`, using only the usual three axioms.

`lake run tensor-c-test` retains actual `add.c`/`mul.c` and their checking logs
in `build/tensor-c/`. It includes one changed-bound rejection and one native
check for shared inputs, output frames, signed underflow and empty execution.
These are file/toolchain boundary checks, not substitutes for the universal
body proofs. Header preprocessing, the native ABI/compiler and hardware remain
outside the authored C semantics.
The gate passed in `build/c-tensor-artifact-gate.log`; both actual-file theorem
audits list only `propext`, `Quot.sound` and `Classical.choice`. The complete
repository gate passed in
[CI for 1007286](https://github.com/CogniPilot/rumoca_lean/actions/runs/34469374951).

Alignment with the Rust typed Solve program is retained: the source/IR contains
one pointwise tensor instruction, while execution traverses storage at runtime.
This increment adds no source scalarization, shape inference, solver choice or
AD lowering in the backend. Rust's register destinations, diagonal instruction
and source spans identify the next storage/provenance interfaces to compose;
the helper proof alone does not establish those connections.

Next, compose prepared tensor program instructions with these helpers through
actual calls and scratch storage, including fills and diagonal output. Bind
declaration metadata to the same kernel and establish input timing, numerical
step and overflow/error policy. FMI dimensions/value references and actual
FMU/eFMU certificates must follow before production accepts either array model.
No further grammar growth is needed to complete these obligations.

## Ordinary calls and initialization/AD fills

`CLoops.Calls` looks up a C function tree, converts the evaluated arguments
using the declared header types, creates a fresh parameter scope, executes
that tree through the existing loop machine, and returns to its continuation.
It reuses `CCalls.parameters` and its pure argument evaluator. `body_reaches`
lifts every existing body transition; no helper name is assigned an assumed
tensor result. The fragment admits discarded void calls with explicit returns.
The binding/scope rules were reviewed against C11 draft
[N1570 §6.5.2.2 and §6.9.1](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf).
This authored subset does not formalize the native ABI, allocation, general
return values or all C call expressions.

`CTensor.bind_parameters` and `bind_types` prove the concrete add/multiply
signatures. `helper_call_correct` covers all behaviors from call entry through
return against the independent `Finite.Pointwise` relation. `invoke_reaches`
also evaluates the generated call's arguments, restores the saved caller
locals/types and continues with the helper's exact heap effects.
`CallArtifactContract` retains the previous text/body/finite/frame proposition
and adds this function-call contract for the same file and operator.

`TensorWriter.writer_reaches` now owns the shared loop/write proof; the existing
binary theorem statements are unchanged. `TensorFill*` uses it to emit and
prove the exact finite tensor fill, including signed zero. The fill signature,
call, generated invocation, independent C token grammar and printer are checked.
`literal_eval` proves the existing shared C zero/one renderer, and
`solve_fill_correct` identifies the target result with the actual Solve fill
program used for initialization and forward AD seeds.

All 21 added roots pass `build/c-tensor-call-fill-audit.log`. The fixed file
adapter now checks the stronger call contracts for add/multiply and the full
fill contract; all three actual files passed `build/c-tensor-call-fill-gate.log`.
One signed-zero fill assertion was added to the existing native boundary check;
no new example model or test matrix was introduced. The earlier local full
gate encountered subsequent in-progress call code; it is not a successful
full-gate record. The hosted run for the fixed `1007286` checkpoint passed.
The required full gate for the call/fill increment is now running in
`build/c-tensor-call-fill-full-gate.log`.

Next, compile the complete prepared instruction sequence with a checked map
from shape-indexed references to disjoint intermediate buffers and a result
reference. Each call must carry the same storage invariant into the next
instruction, including unused intermediates and their arithmetic-domain
obligations. Result storage, dense diagonal materialization, FMI metadata,
overflow/error handling and complete source/archive binding remain open.
