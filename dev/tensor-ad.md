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

## Tensor instance storage bound to the model right-hand side

`FMI3.TensorInstance` gives one tensor model instance a fully typed static object
record for a prepared `Solve.TensorFMI3Model shape`. The record holds the
FMI-visible tensors: the independent time base, the input tensor `u`, the state
tensor `x`, the state derivative `der(x)`, and, when the prepared problem exposes
a dense observation, the output tensor `J`. Each tensor member is a contiguous
array of `double` whose extent is the shape volume; there is no dynamic
allocation. It reuses the shared tensor region machinery
(`CMemory.TensorRegion`) rather than a new memory model: a member array is a
`place`d range of `float64` cells addressed inside one record of the static
instance pool. Records are addressed by an instance index into the pool, so
distinct instances occupy distinct array elements. This mirrors the scalar
adapter's bounded static pool (`StaticStorage`, `deploymentCapacity = 32`); the
storage and separation theorems are universal in the instance index, so any pool
bound applies. Rank and extents stay symbolic; no tensor coordinate is
enumerated. This is a package-checked product only: no production artifact is
emitted, no CLI or grammar case is added, and the scalar adapter and every
existing contract are unchanged.

`FMI3.TensorInstanceRhs` deploys the admitted `TensorSquare` kernel
(`der(x) = u .* u`) into that record. The derivative entry's parameters and
result are pointed at the instance's `x` and `u` (inputs) and `dx` (output)
regions. A well-formed instance heap discharges the tensor derivative entry's
`Arguments.Valid`, `LayoutBound`, `Represents` and `Ready` predicates, so
`FMI3.TensorModelRhs.behaviors` applies. The concluding theorem is universal in
the tensor shape and the instance index: running the derivative entry on an
instance writes the finite tensor derivative into that instance's `der(x)`
region, preserves every cell outside it, and in particular preserves every
tensor cell of every other instance in the static pool. Finite execution of the
ordered arithmetic is an explicit entry premise; storage validity is derived
from the record, not assumed of the caller.

| Obligation | Checked theorem |
| --- | --- |
| The instance's state and input regions are readable | `TensorInstance.reads_state`, `TensorInstance.reads_input` |
| The instance's derivative region is writable | `TensorInstance.writable_derivative` |
| Distinct tensor members of one instance never alias | `TensorInstance.fields_separate` |
| Distinct instances of the pool never alias | `TensorInstance.instances_separate` |
| Preparing one instance preserves every other instance's storage | `TensorInstance.store_other_instance` |
| The derivative buffer resolves to the instance's `der(x)` region | `TensorInstanceRhs.derivativeBuffer_eq` |
| Each named buffer resolves to its member address and count | `TensorInstanceRhs.parameter_bound` |
| The derivative entry runs, writing `der(x)` and preserving other instances | `TensorInstanceRhs.derivative_writes` |

The added roots pass the FMI package axiom audit on the three permitted
foundational axioms. The `TensorInstance` storage and separation theorems are
model-agnostic; `TensorInstanceRhs` binds the concrete admitted kernel, keeping
`RumocaCore.Array` (the development array profile) in a checked package product
without emitting it. The dense output tensor `J` is supported as an optional
record member; the bound derivative demonstration uses the no-output kernel, so
the diagonal observation and non-uniform initialization remain deferred, along
with the FMI lifecycle, numerical overflow/error policy and the complete bound
tensor FMU/eFMU certificates. No wrapper body, metadata or archive contract is
added, and no grammar case is admitted.

## Tensor Float64 accessor bodies over the tensor instance record

`FMI3.TensorFloat64` defines the tensor `fmi3GetFloat64` and `fmi3SetFloat64`
function bodies over one `FMI3.TensorInstance` record, in the same authored C
subset the scalar runtime uses. Each accessor validates the instance handle and
lifecycle guard exactly as the scalar bodies do (`Runtime.require`), then
dispatches one array value reference to a whole instance region under the FMI
3.0.2 array-access rule. The request must name exactly one value reference
(`nValueReferences = 1`); the caller's `nValues` must equal the referenced
variable's element count; the copy uses one counted `size_t` loop whose bound is
that symbolic count, so no tensor coordinate is enumerated. Return status is
`fmi3OK` on success and the scalar code's status on rejection.

The getter dispatches all declared variables: reference `0` denotes the time
base (element count 1), `1` the input `u`, `2` the state `x`, `3` the derivative
`der(x)` (each element count `shape.volume`), and `4` the dense output `J`
(element count `oshape.volume`, present only when the instance record carries the
output; otherwise reference `4` is rejected). The setter dispatches the two
writable variables, input `u` (1) and state `x` (2), validating that every caller
value is finite before any write; references `0`, `3`, `4` and any unknown
reference are rejected. The dispatch stages the region pointer and count into
ordinary locals and runs in the typed call machine (where local assignment is
defined); the guard runs in the memory machine and the two share the reusable
copy core.

This is a package-checked product only: no production artifact is emitted, no
CLI or grammar case is added, and the scalar adapter, `Runtime.lean` and every
existing contract are unchanged. Every theorem is universal in the tensor shape,
the instance index of the static pool, the request lengths and the heap.

| Obligation | Checked theorem |
| --- | --- |
| One getter/setter copy iteration reads and writes one cell | `TensorFloat64.getCopy_step`, `setCopy_step` |
| The copy loop moves exactly the region, row-major | `TensorFloat64.getCopy_reaches`, `setCopy_reaches` |
| The finiteness validation loop accepts every finite value, heap fixed | `TensorFloat64.validate_reaches` |
| Both bodies contain no nested block declarations | `TensorFloat64.getBody_closed`, `setBody_closed` |
| The staged prefix reaches the copy loop for any selected region | `TensorFloat64.get_reaches_of`, `set_reaches_of` |
| The getter's sole terminating behavior per reference (`time`, `u`, `x`, `der(x)`, `J`) | `TensorFloat64.get_behaviors_time`/`input`/`state`/`deriv`/`output` |
| The setter's sole terminating behavior per writable reference (`u`, `x`) | `TensorFloat64.set_behaviors_input`/`state` |
| Each accepted getter reference bound to the instance record | `TensorFloat64.get_instance_behaviors_time`/`input`/`state`/`deriv`/`output` |
| Each accepted setter reference bound to the instance record | `TensorFloat64.set_instance_behaviors_state`/`input` |
| The successful setter preserves every tensor cell of every other instance | `TensorFloat64.set_preserves_other_instances` |
| A null instance handle is rejected with `fmi3Error`, changing nothing | `TensorFloat64.null_get_behaviors`, `null_set_behaviors` |
| The time/output regions are readable and the state region writable | `TensorFloat64.reads_time`, `reads_output`, `writable_state` |
| The input region is writable in the input-writable instance | `TensorFloat64.inputWritableStore_writable` |
| Both bodies print their intended C token grammar | `TensorFloat64.getBody_printable`, `setBody_printable`, `signature_printable` |
| The rendered functions denote themselves under the shared C printer | `TensorFloat64.getFunction_denotes`, `setFunction_denotes` |
| Printed text, closedness, denotation and null rejection as a contract | `TensorFloat64.get_contract`, `set_contract` |

The `written` result is the shared tensor-memory snapshot
(`CMemory.TensorView.written`): the getter's result heap sets exactly the
buffer's element-count cells to the region values in row-major order and
preserves every other cell; the setter's result heap sets exactly instance `i`'s
selected region and preserves every other cell, including every tensor cell of
every other instance in the pool. The `der(x)` getter is stated over the instance
heap after the right-hand side has written the derivative region. Because the
instance record models the input region as read-only, the input-setter
instance theorem is stated over `inputWritableStore`, the instance whose input
region is writable (an instance ready to receive inputs). The printed-text
denotation reuses the shared `CTree.Printer.function_denotes` over a constructed
`FunctionPrintable` witness; the contracts carry it as their `denotes` field.
The added roots pass the FMI package axiom audit on the three permitted
foundational axioms.

Remaining and deferred: multi-reference aggregate requests (a request naming
several variables at once, with `nValues` the sum of their element counts and a
running output offset), which are rejected here (`nValueReferences` must equal 1),
not mishandled; the full memory-machine execution witness for the unknown/
unsupported-reference `fail` path (the dispatch structurally reaches the scalar
`fail` statement, returning `fmi3Error` as the scalar bodies do, before the copy
loop; only the null-handle rejection is proved end to end here); and binding the
bodies to an emitted FMU wrapper with its lifecycle and numerical policy. Parser
acceptance and this package product do not authorize production generation.

## Tensor continuous-state interface bodies over the tensor instance record

`FMI3.TensorContinuousStates` defines the Model Exchange continuous-state
function bodies over one `FMI3.TensorInstance` record, in the same authored C
subset the scalar runtime uses. Each body validates the instance handle and
lifecycle guard exactly as the scalar bodies do (`Runtime.require`, with the
`getStates`/`setStates`/`getDerivatives` commands), checks that
`nContinuousStates` equals the symbolic state volume and that the buffer is
non-null, and then moves a whole tensor region between the caller's `fmi3Float64`
buffer and the instance record with one counted `size_t` loop whose bound is the
symbolic volume; no tensor coordinate is enumerated. The copy core and finiteness
validation loop are reused from `FMI3.TensorFloat64`.

`fmi3GetContinuousStates` copies the state tensor `x` into the caller buffer;
`fmi3SetContinuousStates` validates finiteness of every caller value and then
copies them into `x`; `fmi3GetContinuousStateDerivatives` invokes the prepared
tensor derivative entry on the instance and then copies the written `der(x)`
region into the caller buffer. Each theorem is universal in the tensor shape, the
instance index of the static pool, the request length and the heap. Return status
is `fmi3OK` on success and `fmi3Error` for a null handle.

| Obligation | Checked theorem |
| --- | --- |
| The getter copies exactly the state region in row-major order and changes nothing else | `TensorContinuousStates.get_reaches`, `get_behaviors` |
| The setter validates finiteness, then replaces exactly instance `i`'s state region | `TensorContinuousStates.set_reaches`, `set_behaviors` |
| The successful setter preserves every tensor cell of every other instance | `TensorContinuousStates.set_preserves_other_instances` |
| Each accessor bound to the static instance record | `TensorContinuousStates.get_instance_behaviors`, `set_instance_behaviors` |
| A null handle is rejected with `fmi3Error`, changing nothing | `TensorContinuousStates.null_get_behaviors`, `null_set_behaviors`, `null_deriv_behaviors` |
| The derivative entry writes `der(x)` and preserves every other instance | `TensorInstanceRhs.derivative_writes` |
| The derivative getter's copy suffix delivers the written `der(x)` to the buffer | `TensorContinuousStates.deriv_delivers`, `deriv_instance_delivers` |
| A completed typed loop-call embeds into the observable machine with the identical final heap | `CCalls.Events.loop_call_reaches_events`, `loop_call_behaviors_events` |
| The prepared tensor derivative entry runs in the observable machine | `TensorModelRhs.events_reaches`, `TensorInstanceRhs.derivative_writes_events` |
| The fused derivative getter runs and returns `fmi3OK` in one observable-machine execution | `TensorContinuousStates.deriv_reaches`, `deriv_behaviors` |
| Printed text, closedness, denotation and fused execution as a contract | `TensorContinuousStates.deriv_contract` |
| Every body prints its intended C token grammar and denotes itself under the shared C printer | `TensorContinuousStates.getBody_printable`, `setBody_printable`, `derivBody_printable`, `getFunction_denotes`, `setFunction_denotes`, `derivFunction_denotes` |
| Printed text, closedness, denotation and null rejection as a contract | `TensorContinuousStates.get_contract`, `set_contract` |

The unknown or unsupported value-reference `fail` path of the tensor Float64
getter and setter, left open by the accessor increment, is now proved end to end:
`TensorFloat64.get_fail_prefix`/`set_fail_prefix` execute the memory machine to
the `fail` statement before the copy loop with the heap unchanged, and
`get_fail_behaviors`/`set_fail_behaviors` return `fmi3Error` through
`GuardedCalls.FailurePrefix.silent_behaviors`.

The derivative getter is now delivered as one fused observable-machine execution
(`TensorContinuousStates.deriv_reaches`/`deriv_behaviors`, bundled by
`deriv_contract`), resolving the previously open fused-run item.
`fmi3GetContinuousStateDerivatives` guards the handle/lifecycle, checks the
count, invokes the prepared tensor derivative entry `rumoca_rhs` (resolved
directly by name, saving the copy suffix as the caller continuation), then copies
the written `der(x)` region into the caller buffer, all in the observable call
machine `CCalls.Events.machine`. Its sole terminating behavior returns `fmi3OK`
with the finite tensor derivative delivered to the caller buffer, the instance's
`der(x)` region holding the same values, and every other cell of every other
instance preserved; a null handle returns `fmi3Error` changing nothing.

### The typed-to-observable transfer lemma

The two call machines are the same `CCalls.Typed.nextWith` scheduler over the
same program definitions; they differ only in the call-site `enterCall`. The
typed scheduler reads a direct callee name from the statement, while the
observable scheduler resolves the callee expression through the address
dictionary. On the call-free entry-loop body, on every empty-body return, and on
a nested direct call they agree unconditionally except when the observable
resolution returns a different name; the exact premise capturing agreement is
`CCalls.Events.Resolves`.

The prepared tensor derivative entry runs in the void loop-call machine
`CLoops.Calls.machine` (the level of `CTensor.Lowering.CallCorrect`), whose nested
calls are the emitted tensor helper functions (`rumoca_tensor_mul`, and, for the
initializer, `rumoca_tensor_fill`), all direct calls by identifier that are not
shadowed by constants. The transfer lemma
`CCalls.Events.loop_call_reaches_events`/`loop_call_behaviors_events` (proved in
`packages/backend-c`, the owner of both machines, mirroring
`CCalls.Typed.loop_call_result`; only the call-site lemma changes) embeds the
same completed loop-call execution into the observable machine under any saved
caller, reaching the identical final heap, under `Resolves` for the call sites the
run visits. It changes neither machine definition. `TensorModelRhs.events_reaches`
and `TensorInstanceRhs.derivative_writes_events` apply it to make the prepared
entry's execution, proved in the typed machine (`TensorModelRhs`,
`TensorInstanceRhs.derivative_writes`), available as an observable-machine run
with the identical `der(x)` write and instance-preservation frame.

The fused getter carries the direct-resolution premise (`resolves`) explicitly; a
tensor adapter discharges it for its own emitted helper functions. The tensor
count queries are now delivered (see below). The count-negotiation policy for a
partial or oversized request, and binding the bodies to an emitted FMU wrapper
with its lifecycle and numerical policy, remain open. This is a package-checked
product only: no production artifact is emitted, no CLI or grammar case is added,
and the scalar adapter, `Runtime.lean` and every existing contract are unchanged.

## Tensor count queries, time setter and reset

`FMI3.TensorCountQueries`, `FMI3.TensorSetTime` and `FMI3.TensorReset` define the
Model Exchange count-query, time-setter and reset function bodies over the tensor
instance record, in the same authored C subset the scalar runtime uses, as
package-checked products. Each guards the instance handle and lifecycle exactly as
the corresponding scalar body (`Runtime.require`), and every theorem is universal
in the tensor shape, the instance address (and, for the framing corollaries, the
instance index of the static pool) and the heap.

`fmi3GetNumberOfContinuousStates` writes the symbolic state volume `shape.volume`
as a `size_t` into the caller's pointer, and `fmi3GetNumberOfEventIndicators`
writes `0`. Their sole terminating behaviors, null rejection, closedness,
denotation and a bundling `Contract` are proved universally in the shape under an
explicit `shape.volume < 2 ^ 64` premise. The integer-to-`size_t` conversion of
the count is discharged through the reusable `CLoops.convert_size_nat` lemma (a
shared `CMemory.store_of_convert` step keeps the target cell type abstract), and
the body run is composed from the existing small machine steps rather than one
large reduction, so the `2 ^ 64` bound is never evaluated against the symbolic
volume.

`fmi3SetTime` validates finiteness of the time value and writes it into the
instance's independent time base (the scalar rank-0 member, one `double` cell). Its
successful behavior writes exactly the time cell of instance `i` and preserves
every other cell (`preserves_other_instances`); a non-finite value returns
`fmi3Error` with logging suppressed (`nonfinite_behaviors`, through
`GuardedCalls.FailurePrefix.silent_behaviors`) and a null handle returns
`fmi3Error` changing nothing.

`fmi3Reset` restores the fixed-zero initialization of the state region `x` with a
counted `size_t` loop bounded by the symbolic volume, and resets the time cell to
zero. Its sole terminating behavior writes exactly those cells of instance `i` to
`+0` and preserves every other cell of every other instance
(`preserves_other_instances`); a null handle returns `fmi3Error` changing nothing.
`reads_initialization` proves the post-reset state region reads the fixed-zero
fill, and `initialization_is_zero` identifies that fill with the evaluation of the
prepared IVP's initialization program `fill shape .zero` for the admitted kernel
(`TensorInstanceRhs.kernel`), so the reset re-establishes the initialization
program's value.

| Obligation | Checked theorem |
| --- | --- |
| Count query writes the count and returns `fmi3OK`; null returns `fmi3Error` | `TensorCountQueries.call_behaviors`, `null_behaviors` |
| The `size_t` count conversion stays symbolic against `2 ^ 64` | `TensorCountQueries.store_count`, `CMemory.store_of_convert` |
| Time setter writes the time cell and preserves everything else | `TensorSetTime.call_behaviors`, `preserves_other_instances` |
| Non-finite and null time rejections | `TensorSetTime.nonfinite_behaviors`, `null_behaviors` |
| Reset fills the state region with `+0` and resets time; null returns `fmi3Error` | `TensorReset.reset_behaviors`, `null_behaviors` |
| The post-reset state region reads the initialization program's value | `TensorReset.reads_initialization`, `initialization_is_zero` |
| Reset preserves every cell of every other instance | `TensorReset.preserves_other_instances` |
| Each body prints its C token grammar and denotes itself | `*.body_printable`, `*.signature_printable`, `*.function_denotes` |
| Printed text, closedness, denotation and behaviors as a contract | `TensorCountQueries.contract`, `TensorSetTime.contract`, `TensorReset.contract` |

The added roots pass the FMI package axiom audit on the three permitted
foundational axioms. These are package-checked products only: no production
artifact is emitted, no CLI or grammar case is added, and the scalar adapter,
`Runtime.lean` and every existing contract are unchanged. The count-negotiation
policy for a partial or oversized request and binding these bodies to an emitted
FMU wrapper with its lifecycle and numerical policy remain open.

## Tensor instance lifecycle bodies over the static tensor pool

`FMI3.TensorLifecycleModes`, `FMI3.TensorFree` and `FMI3.TensorLifecycleHistory`
define the Model Exchange mode-transition bodies, the instance-free body and a
composed lifecycle history over the static tensor instance pool, in the same
authored C subset the scalar runtime uses, as package-checked products. Each mode
transition guards the instance handle and lifecycle exactly as the corresponding
scalar body (`Runtime.require`), and every theorem is universal in the instance
address and heap (and, for the framing corollaries and the history, the instance
index of the static pool).

`fmi3EnterInitializationMode`, `fmi3ExitInitializationMode`, `fmi3EnterEventMode`,
`fmi3EnterContinuousTimeMode` and `fmi3Terminate` each run
`Runtime.require cmd ++ [Runtime.setMode after, Runtime.ok]`: after the shared
handle/lifecycle guard they write the single lifecycle-mode cell of the instance
record and return `fmi3OK`. The written mode follows the reference lifecycle table
(`nextMode`): Instantiated → Initialization, Initialization → Event (Model
Exchange), Continuous → Event, Event → Continuous, and Event/Continuous →
Terminated. These bodies are shape-independent: they never read or write a tensor
region, so they are stated over an arbitrary instance address and specialized to
the static pool record only in the framing corollary. A successful transition
changes only the `mode` cell of the addressed instance and preserves every tensor
cell of every other instance (`preserves_other_instances`). A null handle is
rejected with `fmi3Error` changing nothing (`null_behaviors`); a call issued in an
illegal mode reaches the shared `fail` statement and returns `fmi3Error` with
logging suppressed, after entering Terminated as the scalar rejection does
(`illegal_prefix`, `illegal_behaviors`, through
`GuardedCalls.FailurePrefix.silent_behaviors`). The success, null-handle and
illegal-mode behaviors are bundled per transition as a `Contract` mirroring the
scalar `EventEntry.FunctionContract`/`Termination.FunctionContract` shapes.

`fmi3FreeInstance` is entirely model-agnostic: it reads only the reserved slot
index `m->slot` stored at creation and the pool's reservation-flag block, and
performs one atomic store clearing the slot's flag. It is therefore exactly the
shared `StaticRelease.function`, instantiated for the tensor pool record
`TensorInstance.record pool i = pool.index i`. `FMI3.TensorFree` re-exports the
shared release theorems specialized to the tensor pool and bundles them as a
`Contract` mirroring the release portion of the scalar
`StaticRuntime.FunctionContract`: releasing an owned slot discharges exactly its
lease, restores the owner map to `update owners slot none`, performs one atomic
store, preserves every other cell and returns void (`free_owned`); a null handle
changes nothing (`null_behaviors`).

`FMI3.TensorLifecycleHistory.lifecycle_history` composes one small history over the
pool. From a created, Instantiated-mode instance record (the factory
postcondition, supplied as explicit cell premises), the two initialization-mode
transitions thread into Event Mode by two single-cell mode writes, and from the
reached Event-Mode heap the instance answers one continuous-state derivative query
(`TensorContinuousStates.deriv_contract`) and is released by `fmi3FreeInstance`. It
derives the observed status of each call (`fmi3OK` for the two mode transitions and
the derivative query, void for free) and the pool's final owner map (the released
slot restored to unowned). The derivative query and the free act on disjoint memory
(the instance tensor regions and the pool's reservation-flag block), so both issue
from the reached Event-Mode heap; the premises are kept explicit (the
created-instance record cells, the finite kernel execution and direct-resolution
premise the derivative query needs, the identification of the reached Event-Mode
heap with a well-formed tensor instance heap, and the reservation-flag
representation and release bindings the free needs).

| Obligation | Checked theorem |
| --- | --- |
| Each mode transition writes only the mode cell and returns `fmi3OK` | `TensorLifecycleModes.body_run`, `call_behaviors` |
| A null handle is rejected with `fmi3Error`, changing nothing | `TensorLifecycleModes.null_behaviors`, `TensorFree.null_behaviors` |
| An illegal mode reaches `fail` and returns `fmi3Error` with logging suppressed | `TensorLifecycleModes.illegal_prefix`, `illegal_behaviors` |
| A successful transition preserves every cell of every other instance | `TensorLifecycleModes.preserves_other_instances` |
| Free releases exactly the owned slot and restores the owner map | `TensorFree.free_owned` |
| Each body prints its C token grammar and denotes itself | `TensorLifecycleModes.body_printable`, `signature_printable`, `function_denotes` |
| Printed text, closedness, denotation and behaviors as a contract | `TensorLifecycleModes.contract`, `TensorFree.contract` |
| Composed create-through-free lifecycle statuses and final owner map | `TensorLifecycleHistory.lifecycle_history` |

The added roots pass the FMI package axiom audit on the three permitted
foundational axioms. These are package-checked products only: no production
artifact is emitted, no CLI or grammar case is added, and the scalar adapter,
`Runtime.lean` and every existing contract are unchanged.

## Tensor instance creation over the static tensor pool

`FMI3.TensorInstanceInit` and `FMI3.TensorFactory` define the Model Exchange and
Co-Simulation instance-creation bodies over the static tensor instance pool, in the
same authored C subset the scalar runtime uses, as package-checked products. The
tensor factory shares the scalar factory's model-agnostic reservation prefix and
its name/token admission prefix; only the reserved-record initializer differs.

`FMI3.TensorInstanceInit` is the reserved-record initializer. After the reserved
array element is selected, it stores the reserved slot index `m->slot`, writes the
FMI lifecycle metadata (`kind`, mode `Instantiated`, the captured environment and
logger, the logging flag), resets the independent time base to `+0`, and zero-fills
the state region `x` with the same counted `size_t` loop the tensor reset uses
(`TensorReset.zeroBody`), then returns the record cast to `fmi3Instance`. The
metadata block runs as single-cell stores in the bounded body machine and is lifted
into the observable call machine; the state fill and handle return complete in the
same call machine (`TensorInstanceInit.return_reaches`, bundled by `complete`). The
loop bound is the symbolic state volume, so no tensor coordinate is enumerated, and
the `2 ^ 64` size bounds stay abstract. The post-initialization state region reads
the fixed-zero fill, which is the evaluation of the admitted kernel's initialization
program `fill shape .zero` (`reads_state`, `TensorReset.initialization_is_zero`).
The initialized record exposes the metadata and state values the lifecycle,
derivative and free bodies consume (`initialized`, `Initialized`), and creation
touches only the reserved record's own cells, preserving every cell outside it
(`frame`) and every cell of every other pool instance (`other_instance`).

`FMI3.TensorFactory` composes the creation behaviors at the same reservation `Scope`
premise level as the scalar `StaticFactory.successful`. `fmi3InstantiateModelExchange`
and `fmi3InstantiateCoSimulation` are the `kind`-parameterized
`TensorFactory.function model shape kind`. Reusing the shared reservation lemmas
(`StaticFactory.reserve`, `guard`, `selectInstance`, `select_step`, `guard_step`,
`ReservationBindings`) and the `CAtomicScan` helper, the reservation body enters the
atomic scan, checks capacity, selects the reserved element, and runs the tensor
initializer. Successful creation returns a handle to a slot that was free,
initializes exactly that record and preserves every other slot and every other
instance's tensor regions, performing only the scan's bounded atomic work
(`successful`); it marks the reserved slot owned in the reservation-flag block
(`successful_owned`, whose postcondition `Created` supplies the created `kind`, mode
`Instantiated` and `slot` cells). Exhaustion returns null and changes no record
(`exhausted_silent`). Ownership is preserved through the initializer because it only
writes the reserved record's own cells (`initialized_owners`), so a created slot can
be released (`Created.release`), and a creation followed by a release restores the
original slot ownership and reusable storage (`create_release`).

The admission prefix is reused, not reauthored: the tensor factory function is the
shared `FactoryPrefix.body model kind (TensorFactory.code shape kind)`, parameterized
over the model only through its instantiation `token` string. An accepted identity
reduces the public call to the tensor reservation body (`admission_accepts`, reusing
`FactoryValidation.admission_equivalence`); a bad instance name or instantiation
token returns null with the documented `"Invalid name or instantiation token"`
logging and no reservation (`rejected_silent`, reusing
`FactoryValidation.rejected_silent`); the Co-Simulation capability guard rejects
requested event mode and intermediate updates outside the admitted profile, exactly
as the scalar prefix. No identity-validation proof is duplicated. The creation,
exhaustion, ownership, admission and rejection guarantees are bundled as a
`FunctionContract` mirroring the creation portion of `StaticRuntime.FunctionContract`
and the admission/rejection portion of `FactoryAdmission.FunctionContract`.

`FMI3.TensorLifecycleHistory.lifecycle_from_creation` strengthens the composed
lifecycle history to start from an initial free pool and the proved reservation-body
creation call rather than a supplied created-record premise: the creation reserves
the free slot, initializes the record and marks it owned, and its postcondition
supplies the created-instance cells the two Initialization-mode transitions and the
free consume. The history proceeds create, enter/exit Initialization Mode, one
continuous-state derivative query, and free, deriving the returned handle, the
observed statuses, and the final owner map equal to the original free pool.

| Obligation | Checked theorem |
| --- | --- |
| The metadata block runs to the metadata heap without evaluating the 64-bit bound | `TensorInstanceInit.metaCode_run` |
| The initializer runs to the returned handle and initialized heap, preserving other cells | `TensorInstanceInit.return_reaches`, `complete` |
| The initialized record exposes the metadata and zero-filled state values | `TensorInstanceInit.initialized`, `reads_state` |
| Creation touches only the reserved record; other cells and other instances are preserved | `TensorInstanceInit.frame`, `other_instance`, `Storage.preserved` |
| Successful creation returns an initialized handle to a free slot, marking it owned | `TensorFactory.successful`, `successful_owned` |
| Exhaustion returns null and changes no record | `TensorFactory.exhausted_silent` |
| A created slot is released; create-then-release restores the pool | `TensorFactory.Created.release`, `create_release` |
| An accepted admission reduces to the reservation body; bad name/token is rejected | `TensorFactory.admission_accepts`, `rejected_silent` |
| Creation, exhaustion, ownership, admission and rejection as a contract | `TensorFactory.contract` |
| The lifecycle history started from a proved creation call | `TensorLifecycleHistory.lifecycle_from_creation` |

The added roots pass the FMI package axiom audit on the three permitted
foundational axioms. These are package-checked products only: no production
artifact is emitted, no CLI or grammar case is added, and the scalar factory,
`Runtime.lean` and every existing contract are unchanged.

Remaining and deferred: the count-negotiation policy for a partial or oversized
request, and binding these bodies to an emitted FMU wrapper with its lifecycle and
numerical policy, remain open. This package product does not authorize production
generation.

## Tensor nominal-value getter over the symbolic state volume

`FMI3.TensorNominals` defines the tensor `fmi3GetNominalsOfContinuousStates` body
over the static tensor instance record as a package-checked product. The scalar
body assumes a single continuous state and writes the fixed nominal `1` into
`nominals[0]` after checking `nContinuousStates == 1`. The tensor profile carries
the symbolic state volume, so this body validates the instance handle and lifecycle
guard exactly as the scalar body does (`Runtime.require` with the `getNominals`
command), checks that the request count equals the symbolic state volume
`shape.volume` and that the caller buffer is non-null (`countReject`), and then
writes the fixed nominal `1` into every cell of the caller buffer with a counted
`size_t` loop whose bound is the symbolic volume. The loop bound is the symbolic
volume, so no tensor coordinate is enumerated during lowering. The integer literal
`1` converts to the exact binary64 value `Binary64.one`.

The function shares the scalar public signature `ErrorCalls.nominalSignature`, so
the emitted prototype is the pinned header prototype. The single-cell fill step
reuses the shared `TensorFloat64` copy-cell address lemmas (`dstCell`,
`dstCell_lvalue`), and the counted loop reuses the shared loop scheduler
(`CCalls.Events.loop_reaches`) and pending-output storage lemma
(`Float64Calls.pending_output`) that the tensor reset and continuous-state bodies
use. Its sole terminating behavior on the observable call machine
`CCalls.Events.machine` returns `fmi3OK` and leaves the caller buffer reading the
fixed nominal `1` in every cell, with every cell outside the buffer preserved
(`preserves_instance`); a null handle returns `fmi3Error` changing nothing
(`null_behaviors`).

| Obligation | Checked theorem |
| --- | --- |
| One fill iteration writes `1` into the staged buffer cell | `TensorNominals.oneCopy_step` |
| The counted loop fills the whole caller buffer with `1` | `TensorNominals.oneCopy_reaches` |
| The request check passes for a matched non-null request | `TensorNominals.count_pass` |
| The getter runs, writes `1` to every buffer cell and returns `fmi3OK`; null returns `fmi3Error` | `TensorNominals.nominal_behaviors`, `null_behaviors` |
| The filled buffer reads the fixed nominal `1` in every cell | `TensorNominals.reads_nominals` |
| The fill preserves every cell outside the caller buffer | `TensorNominals.preserves_instance` |
| Printed prototype, closedness, denotation and behaviors as a contract | `TensorNominals.signature_printable`, `body_printable`, `function_denotes`, `contract` |

The added roots pass the FMI package axiom audit on the three permitted
foundational axioms. Every theorem is universal in the tensor shape, the instance
address, the caller buffer and the heap. This is a package-checked product only: no
production artifact is emitted, no CLI or grammar case is added, and the scalar
adapter, `Runtime.lean` and every existing contract are unchanged.
