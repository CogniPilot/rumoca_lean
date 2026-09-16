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

### Sparsity sequencing

Preserve structure now; implement general sparsity after the existing tensor
FMU round. `Solve.Tensor.DiagonalProgram` already keeps the coefficient program
and diagonal operation separate. Retain that representation through lowering;
materialize a dense matrix only for an explicit output that requires it. Keep
JVP/VJP execution independent of dense Jacobian storage. This does not require
new grammar or a general sparse container in the current increment.

The later analysis belongs with Solve and AD, with backend consumers of its
checked result. Its first obligation is structural-zero soundness: every
omitted entry is zero throughout the admitted domain, not merely at one sampled
input. A conservative pattern may retain extra entries but must not omit a
possible dependency. Sparse storage must refine the same tensor denotation;
compressed derivative evaluation must preserve the derivative action and the
chosen finite-arithmetic/error contract. In particular, removing an unused
operation must not silently remove an overflow required by the existing ordered
execution semantics. CSR/CSC storage, coloring and sparse solvers remain deferred.
Rust's `rumoca-eval-solve/src/sparsity.rs` is a design reference for deriving
patterns from the owned Solve program and conservatively retaining dependencies.

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
The required full gate for the call/fill increment passed locally in
`build/c-tensor-call-fill-full-gate.log` and in
[CI for e89e4f4](https://github.com/CogniPilot/rumoca_lean/actions/runs/34471779750).

Next, compile the complete prepared instruction sequence with a checked map
from shape-indexed references to disjoint intermediate buffers and a result
reference. Each call must carry the same storage invariant into the next
instruction, including unused intermediates and their arithmetic-domain
obligations. Result storage, dense diagonal materialization, FMI metadata,
overflow/error handling and complete source/archive binding remain open.

## Complete prepared tensor programs

`CTensor.Lowering` now maps shape-indexed Solve references to buffer/count
expressions. A storage plan supplies one fresh destination per instruction;
`emit` emits one fill or binary helper call and retains a shaped result
reference. `emit_code_count` proves that code size depends only on the number
of instructions, with no tensor-coordinate expansion.

`Ready` checks all destinations against the initial heap and all prior
registers. `represents_written` extends the register interpretation after an
instruction, including references of different shapes. `ready_written` proves
that the write preserves the remaining destinations. `emit_correct` composes
the actual argument evaluation, ordinary calls, finite arithmetic and writes
across the whole sequence. `emit_refines` states that every target behavior
terminates with the independently specified finite Solve result and the full
memory frame. Its arithmetic-domain premise includes unused intermediates.

The proof currently assumes caller-supplied valid storage and pointer/count
expressions whose bindings do not depend on mutable heap contents. It starts
at the prepared function body; it does not establish an allocator, the outer
function's call ABI or a production FMI lifecycle. Dense diagonal output,
concrete source/kernel storage and metadata, overflow/error policy and the
complete tensor FMU/eFMU certificates remain required before admission.

The corresponding independent token grammar validates target identifiers,
parameter uniqueness, helper-name shadowing, argument scope and pointer
mutability. Its structural printer theorem covers arbitrary valid functions.
The actual-file contract binds the same target body to finite Solve execution
and identifies the output buffer. The single boundary fixture consumes the
existing AD-generated square coefficient program; it does not substitute a
hand-written `2*u` computation. Its certificate quantifies over all shapes.

All 22 new roots pass the unchanged axiom audit in
`build/c-tensor-program-gate.log`. That gate also certifies the actual complete
`build/tensor-c/program.c`, rejects an altered operator and checks native
coefficient execution with externally supplied helper prototypes. The exact
file theorem is audited in `build/tensor-c/program-contract.log`. The full
repository gate passed in `build/c-tensor-program-full-gate.log` and in
[CI for 08b8a7d](https://github.com/CogniPilot/rumoca_lean/actions/runs/34476481293).

Review against Rust's `typed_program/program.rs` confirms the shared design:
typed tensor registers, explicit destinations and a result register. Rust also
retains region/operation provenance and a distinct diagonal operation. Their
storage/metadata and source-span connections remain obligations here; the
small C emitter does not perform AD, DAE solving or source-name resolution.

## Complete call entry and supplied storage

`TensorProgramParameters` proves conversion and scope binding for arbitrary
valid tensor signatures. `program_call_reaches` executes entry into the actual
function, all nested helper calls and the ordinary return. `program_call_refines`
characterizes every complete call behavior by the finite Solve result and the
memory frame. `CallArtifactContract` retains the prior grammar/body contract
and adds this outer-call theorem for the same emitted text.

`TensorRegions` supplies symbolic typed object regions and proves initialized
reads, writable scratch ranges and separation of distinct fields for arbitrary
shapes. `TensorCChecks.Entry` uses them for the existing square coefficient
program. It derives argument validity, input representation and every scratch
invariant from its concrete initial heap and the count bound. Its complete-call
theorem no longer asks the consumer to supply low-level storage invariants for
that profile. The fixed actual-file checker now includes this storage contract
and the general outer-call contract, keeping every earlier conjunct.

These proofs specify initial objects; they do not execute allocation or prove
native object lifetime, struct byte layout or ABI linkage. Finite execution of
all ordered intermediates and the external helper/header definitions remain
explicit premises. Dense diagonal output, FMI storage/metadata and lifecycle,
overflow/error policy and complete source-to-archive composition remain open.

All 34 new roots pass the unchanged axiom audit in
`build/c-tensor-entry-gate.log`. The same gate passes the strengthened actual-file
certificate, altered-operator rejection and the existing native boundary check;
no new native test case was needed. The exact file root is audited in
`build/tensor-c/program-contract.log`. The required full gate for this increment
passed in `build/c-tensor-entry-full-gate.log` and in
[CI for 6d4ec7c](https://github.com/CogniPilot/rumoca_lean/actions/runs/34479402664).

## Diagonal C output

The dense-output helper consumes the prepared diagonal coefficients. It calls
the already proved fill helper with positive zero, then copies each coefficient
to its diagonal location. Its C code is independent of the tensor extents;
the compiler does not enumerate coordinates. The storage proof reuses mathlib's
matrix index equivalence and proves exact bit preservation, off-diagonal zeros
and the full memory frame. Empty shapes are included. From a matrix cell count
fitting the authored 64-bit `size_t`, `counter_bounds` and `position_bounded`
derive all dimension/stride/index bounds, including the final unused offset.

`CLoops.sizeAdd` specifies unsigned modulo addition for declared size values,
and `eval_sizeAdd` proves the loop's actual expression cannot wrap under those
bounds. This rule follows
[C11 N1570 §6.2.5](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf).
`Diagonal.helper_call_correct` covers all complete call behaviors;
`invoke_reaches` restores the caller's scope with the exact matrix heap effects.
`Diagonal.SolveContract` identifies that buffer with the actual prepared Solve
diagonal evaluation, given the independent finite coefficient execution.
The fixed helper-file adapter now checks this contract plus the independently
specified complete token grammar against `build/tensor-c/diagonal.c`.

All 35 new roots pass the unchanged axiom policy. The actual-file/native gate
passed in `build/c-diagonal-gate.log`; the exact root is audited in
`build/tensor-c/diagonal-contract.log`. The existing native fixture materializes
its actual AD coefficients as `[[4, 0], [0, 6]]` and checks the output boundary.
No new source model, grammar case or negative-test matrix was added.
The full gate for this increment passed in `build/c-diagonal-full-gate.log`
and in [CI for 8a3b902](https://github.com/CogniPilot/rumoca_lean/actions/runs/34483284726).

Review against Rust's `typed_program/program.rs` again confirms a compact
`Diagonal { destination, operand }` operation, with its operand and destination
handled as typed registers. The Lean helper follows that ownership: it writes
the prepared operation, without deriving AD rules, shapes or a solver.
The coefficient producer and materializer are now composed as described below.
Next, bind the resulting storage/metadata to FMI and prove its
numerical/error and lifecycle policy before the complete FMU/eFMU artifact gate.
General sparsity remains after this round, as recorded above.

## Complete Jacobian C function

`Lowering.emitDiagonal` consumes the prepared coefficient program and explicit
diagonal operation. Its code-size theorem counts one call per Solve operation,
independently of tensor extents. `Reserved` separates the matrix output from
entry registers and coefficient destinations; `reserved_result` and
`reserved_writable` carry those obligations through coefficient execution.
`emitDiagonal_correct` then composes the actual calls and matrix writes.
`diagonal_call_refines` covers parameter conversion, fresh entry scope, every
helper call and ordinary return, with all complete behaviors terminating in
the exact Solve matrix heap. The coefficients survive materialization and the
combined memory frame protects all other cells.

The general `DiagonalArtifactContract` includes independently specified C
tokens, a scoped signature, the exact emitted body and complete-call behavior.
`ProgramFixture.DiagonalEntry` establishes its storage premises for the existing
AD example: named input/scratch/matrix objects, arbitrary backing heap and
arbitrary tensor shape. The actual-file adapter now checks this complete
Jacobian function, including that storage theorem. The existing native fixture
calls the same function; its separate coefficient-only entry was removed.

All 23 added roots and the actual-file/native gate pass in
`build/c-diagonal-model-gate.log` with the unchanged axiom policy. The exact file
root is audited in `build/tensor-c/program-contract.log`; the full gate passed in
`build/c-diagonal-model-full-gate.log` and in
[CI for f63d69a](https://github.com/CogniPilot/rumoca_lean/actions/runs/34487668082).
This is the Jacobian function, not yet
the complete IVP: RHS/initialization output binding, finite overflow/error
policy, FMI storage/metadata/lifecycle and source-to-archive composition remain
open. Initial symbolic object storage and external helper/header definitions
remain premises; no allocator, native ABI or machine-compilation proof is added.

## Prepared IVP C product

`Lowering.Named` renders the existing typed Solve instruction sequence using
named buffers and count parameters. Its structural theorem proves that erasing
the names produces exactly the existing C call sequence and result reference.
The general call/printer contracts therefore apply to constructed functions;
callers no longer need to hand-author a second statement list. The named plan
still contains one destination per tensor instruction, independent of volume.
Runtime construction and semantic proofs are separate modules.

`PointwisePlan` attaches initial, derivative and optional diagonal entries to
one prepared `Solve.PointwiseIVP`. Its complete-file contract covers each member,
requires distinct entry names and excludes helper collisions. This is target
storage/signature annotation, with no source resolution, AD synthesis or solver
selection. `PointwisePlan.correct` composes the existing semantic and printer
theorems for every such valid product.

The actual-file fixture now emits `initial.c`, `derivative.c` and `jacobian.c`
from this product for the existing square/Jacobian model. Its exact proposition
retains the Jacobian contract and adds initializer/RHS call-storage theorems.
They quantify over arbitrary tensor shapes and heaps, deriving the lowerer's
entry predicates from typed readable inputs and writable outputs. Their memory
frames preserve every cell outside the corresponding state/derivative range.
The existing native check invokes initialization, RHS and observation on that
same model. There is no additional source example or rejection matrix.
The package build passes in `build/c-ivp-package.log`. All 22 added roots and
the actual-file/native gate pass in `build/c-ivp-gate.log`; the exact three-file
theorem is audited in `build/tensor-c/ivp-contract.log`. The required full gate
passed in `build/c-ivp-full-gate.log` and in
[CI for e1a734b](https://github.com/CogniPilot/rumoca_lean/actions/runs/34491283172).

## Typed calls and caller composition

`CCalls.Typed` combines typed tensor statement execution with ordinary returned
values and destinations. A callee receives converted parameters and their types;
its actual tree or previously specified numerical statements execute. Returning
restores the saved caller scope, including declared local types. Header bindings,
pure call arguments and the definition table remain explicit. Allocation,
indirect/effectful nested calls and native ABI/linking are outside the fragment.

`loop_step` proves a stepwise embedding of every successful tensor call-machine
transition. `append_reaches` composes its terminating execution with an arbitrary
caller, with a zero-step transition at the old closed terminal. `CallResult`
combines this contextual completion with the exact standalone outcome.
`invoke_return_reaches` then executes an ordinary call and the caller's actual
return expression/conversion, including status-returning contexts. This does
not assume an operation's result from its helper name.

The generic program and diagonal contracts now preserve their result-buffer
and memory-frame guarantees in this machine. The existing IVP file proposition
requires these contracts in addition to every previous conjunct; its checker
continues to bind the same three actual C files. No grammar case, emitted
computation or native regression model is added.

All 22 new roots, the exact-file certificate, existing mutation controls and
native boundary check pass in `build/c-typed-gate.log`, using the unchanged
axiom whitelist. The file root is audited in `build/tensor-c/ivp-contract.log`;
the package build passes in `build/c-typed-package.log`. The required complete
gate passed in `build/c-typed-full-gate.log` and in
[CI for 2e53e66](https://github.com/CogniPilot/rumoca_lean/actions/runs/34494402729).

## Tensor model right-hand-side contract

`FMI3.TensorModelRhs` states the derivative entry of a prepared
`Solve.PointwiseIVP` as an FMI-side function contract in the shape of the scalar
`ModelRhs.FunctionContract`: the printed function, its lexical denotation and
its execution under the typed tensor call machine. `reaches` and `behaviors`
follow from `PointwisePlan.correct`; under any saved caller the machine returns
`void` with the finite tensor derivative in the output buffer and every cell
outside that region preserved. The statements are universal in the tensor
shape, heap and storage; storage validity is supplied at entry. The three roots
are audited in the FMI package checks. No wrapper body, metadata, lifecycle or
archive contract is added, and no grammar case is admitted.

Next, compose the actual tensor wrapper bodies over this contract. Bind instance storage and metadata
to the same prepared IVP, establish its finite overflow/error and lifecycle/time
policy, and compose the source-to-archive certificate. General sparsity and
further grammar remain deferred. The typed call theorem alone does not establish
an allocator, ABI, solver, FMI lifecycle or complete FMU/eFMU contract.

## Tensor FMI 3 model description

`FMI3.TensorMetadata.modelDescription` builds an FMI 3 model description for a
prepared `Solve.TensorFMI3Model shape`, universally over the tensor shape: rank
and extents stay symbolic and no coordinate is enumerated. It is a
package-checked product only. It is not emitted by production, adds no CLI or
grammar case, and leaves the existing scalar unit `modelDescription` and every
existing contract unchanged.

The document declares the independent time base, the input tensor `u`, the state
tensor `x` (`initial="exact"` from the prepared fixed-zero initialization), the
derivative tensor `der(x)` (referencing the state's value reference), and, when
the prepared problem carries a diagonal observation, the dense output tensor `J`.
Each tensor variable is one `Float64` declaration carrying one `Dimension` per
extent with a constant `start`; the output's dimensions come from the state
element count squared. `ModelStructure` lists the output, the continuous-state
derivative and the initial unknowns, each with an explicit `dependencies="1"`
and `dependenciesKind="dependent"` recording the single input dependency (`u`).
Value references are one per variable (`time`, `u`, `x`, `der(x)`, `J`). Per the
FMI 3.0.2 array `start` rule, the `start` attribute of an array variable is a
space-separated list of one value per element (the product of the `Dimension`
starts); `u` and `x` render the profile's uniform fixed-zero initialization as
that flattened list.

| Obligation | Checked theorem |
| --- | --- |
| Decimal extents are printable XML text | `TensorMetadata.text_toString` |
| Array `start` lists one value per element | `TensorMetadata.startEntries_length` |
| The array `start` list is printable XML text | `TensorMetadata.startValue_text` |
| The document is a well-formed tree under the in-tree validator | `TensorMetadata.valid` |
| The document is accepted by the renderer/syntax `Document` relation | `TensorMetadata.document` |
| Value references are pairwise distinct | `TensorMetadata.valueReferences_nodup` |
| Dimension starts recover the declared extents | `TensorMetadata.dimStarts_dimensions` |
| Each variable's Dimension starts multiply to its tensor element count | `TensorMetadata.stateVar_dim_product`, `inputVar_dim_product`, `derivativeVar_dim_product`, `outputVar_dim_product` |
| The derivative's `derivative` attribute references the state's value reference | `TensorMetadata.derivative_references_state` |
| Every `ModelStructure` entry references a declared variable | `TensorMetadata.structure_references_declared` |
| Every `dependencies` reference is a declared variable's value reference | `TensorMetadata.structure_dependencies_declared` |
| Model identifiers decode exactly as the unit document | `TensorMetadata.modelIdentifiers_decode` |

The well-formedness theorems are universal in a printable model name
(`XML.Text` of the name). The element count is `Tensor.Shape.volume`, so the
Dimension-start product theorems reduce to `shape.dimensions.foldr (·*·) 1` for
`u`, `x` and `der(x)`, and to `shape.volume * shape.volume` for `J`; the array
`start` list has that same `shape.volume` many entries. The identifiers decode
through the same `FMI3.decodeModelIdentifiers` used for the unit document, over
the shared `ModelExchange`/`CoSimulation` model-identifier structure. Each
`ModelStructure` entry in this profile lists exactly one dependency reference,
the input `u`.

The added roots pass the FMI package axiom audit on the three permitted
foundational axioms. `Rumoca.Tests.TensorMetadataFixture.fixture_document`
audits the concrete `TensorSquare` shape rendering to a well-formed document,
and the native regression executable ties the actual `ArrayCompiler.prepare`
kernel to that fixture by rendering the same bytes. No production artifact is
emitted; general non-uniform initialization and the bound tensor FMU/eFMU
certificates remain deferred.
