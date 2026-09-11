# Shared C backend

This package consumes prepared Solve programs. It owns the C syntax trees,
printers, lexical/token specifications, numerical and object-memory execution,
call semantics, and their proofs. It has no dependency on either FMI backend
or the compiler driver. It does not perform DAE lowering, impose GALEC
restrictions, infer shapes or choose a solver.

The two paths are:

```text
DAE → GALEC IR → Solve algorithm → C → eFMI wrapper and package
DAE → numerical Solve product  → C → FMI 3 wrapper and package
```

GALEC text is another rendering of the checked GALEC product. It is not the
input to C generation. The tiny core currently has distinct `Solve.Model`
and `Solve.Algorithm.Program` representations; extracting this package does
not unify those types or broaden their accepted language. Both preserve
source/IR evidence and have their own composed correctness contracts.

| Modules | Responsibility |
| --- | --- |
| `Codegen`, `Execution`, `Lowering`, `Statements` | Numerical Solve emission and ideal/IEEE execution, scoping, control and behavior proofs |
| `Syntax`, `SyntaxProofs`, `PrinterProofs` | Independent numerical C grammar, unique denotation and structural printer proof |
| `Tree` | Structured C expressions, declarations and functions used by both wrappers |
| `Origins`, `OriginProofs`, `Provenance` | Complete expression annotations and C-owned rules with checked upstream source ancestry |
| `InitializationCode`, `InitializationOrigins`, `InitializationOriginProofs` | Required origins on prepared initialization emission, with a composed annotation, ancestry and C-body behavior theorem |
| `SourceMap`, `MappedExpression`, `InitializationMap` | Indexed UTF-8 documents, exact expression-printer correspondence and initializer map/execution preservation |
| `StatementOrigins`, `FunctionOrigins`, `MappedStatement`, `MappedFunction` | Complete C annotations and exact mapped statement/signature/function printing |
| `StringLiteral` | Independent C literal denotation, unique UTF-8 payload decoding and preprocessing-safe string printing |
| `Character`, `ReadOnly`, `LiteralStorage`, `LiteralPointers` | Character representation, immutable symbolic objects and literal-pointer evaluation |
| `LiteralLowering`, `LiteralLoopLowering`, `LiteralCallLowering` | Literal-to-name transformation and all-behavior preservation through bodies, loops and calls |
| `LiteralInterface`, `LiteralInterfaceCalls`, `LiteralPool*` | Global lookup preservation, checked name/text pools, symbolic storage construction and composed call preservation |
| `LiteralCollection`, `LiteralNames` | Complete literal collection and checked-constructor name/coverage facts |
| `LiteralDeclaration`, `LiteralDeclarationBlock` | Independent static-array declaration syntax, complete-block printing and initializer-to-storage proofs |
| `Memory`, `Body`, `Calls` | Typed symbolic subobjects, small-step body execution and ordinary calls |
| `BooleanProofs` | Composition of Boolean-valued expressions using the existing short-circuit semantics |
| `Interface` | Explicit dictionary of header constant/type bindings |
| `Arithmetic` | Finite binary64 addition and multiplication for Solve expressions |
| `Algorithm` | Thin emission of prepared tensor Solve instructions |
| `LoopCode`, `Loops`, `LoopProofs` | Counted C loops, declared local types and compositional execution proofs |
| `LoopCalls`, `TensorCalls` | Ordinary void calls, parameter conversions and restoration of caller locals/types |
| `TensorWriter` | Shared counted-write, output-initialization and frame proof |
| `TensorCode`, `TensorMemory`, `TensorProofs` | Shape-independent pointwise helpers, writable output ranges and complete body execution |
| `TensorSyntax`, `TensorContract`, `TensorArtifactCheck` | Independent helper token grammar, finite Solve/text contract and actual-file certificates |
| `TensorCallContract`, `TensorFill*` | Stronger call/file contracts and exact Solve initialization/seed fills |
| `Identifier` | Shared C11 identifier and lexical facts used by target printers |
| `TensorProgramCode`, `TensorProgramMemory`, `TensorProgramProofs` | Shaped storage plans, thin whole-program emission and finite execution/frame proofs |
| `TensorProgramSyntax`, `TensorProgramPrinter`, `TensorProgramContract` | Independent scoped function grammar, structural printer and complete-body artifact contract |

`CInterface` is a parameter of the shared execution definitions. There is no
global default instance. Each adapter proof selects its dictionary locally;
FMI 3 names and eFMI header aliases belong to those adapters. There is one
implementation of the shared machine, with universal execution/lifting proofs.
Adapter body and actual-artifact contracts select the appropriate dictionary.

The shared initializer now returns a checked `Emission`; FMI creation/reset
consume its statement projection. Its preservation theorem assumes supplied
writable binary64 storage. Its fragment map now preserves exact printer bytes,
source ancestry and byte extraction. Complete C-function origins, whole-file
and archive-member maps, allocation and enclosing public-API composition remain open.

The initializer derives a complete statement trace and uses the shared statement
mapper. Generic function maps preserve supplied annotations and exact printer
bytes; correct source/rule attachment by each production emitter remains a
separate requirement. They do not certify arbitrary C-tree validity or execution.

`CString.render_correct` proves that every string expression emitted by `Tree`
has exactly its UTF-8 payload bytes followed by C's terminating zero, including
embedded zeros and empty strings. Question marks are escaped to prevent C11
trigraph replacement; all other nonprinting/non-ASCII bytes use three-digit
octal escapes. The proof covers any sequence of the modeled trigraph and line
splice rewrites under the eight-bit ASCII C profile. Its deterministic decoder
is only a proof device. Static object storage, pointer decay, surrounding
declarations and whole-adapter text/execution require separate contracts.

The literal modules construct immutable symbolic objects and a checked named
pool. `CLiteral.Pool.invocation_behaviors` preserves every call observation
when the pool is added to the interface and literals are lowered to data names.
Source-name collection establishes local freshness and unchanged old lookups;
header exclusions and definition-table binding remain explicit. The production
renderer does not yet use this pass. The declaration printer now has a separate
independent syntax and exact initializer-byte contract, including boundaries
between declarations under the modeled trigraph/splice rewrites. Its storage
theorem binds those decoded bytes to constructed immutable symbolic arrays.
Whole-translation-unit composition, actual-file binding, complete header
exclusions and native storage/layout remain open obligations.

The current tensor C storage profile rejects unsupported ranks without
scalarization. `Algorithm` emits instructions and receives register names and
store locations from its wrapper. eFMI retains its Startup/Recalibrate/DoStep
signatures, complete-function printer contract, and metadata. FMI 3 retains
its public APIs, lifecycle proofs and packaging. These interfaces do not
license arbitrary C trees: each emitted profile still needs its own grammar,
execution and actual-byte certificate.

The development tensor helpers execute addition and multiplication in one
runtime loop per tensor operation. Their universal theorem covers every
coordinate and all body behaviors, allowing the input buffers to alias each
other while requiring a separate writable output range. Every cell outside
that output range is preserved. Loop counters have the authored unsigned
64-bit semantics, with a proof that the admitted count cannot cause wrapping.
Loop/branch bodies contain no local declarations, so flattening their control
flow does not erase an active block scope.

`CTensor.CallArtifactContract` retains the body-level `ArtifactContract` and
also executes ordinary call entry, parameter conversions and return. Its
conditions include a supplied definition-table binding, supported header
types, readable finite inputs, valid output storage and no arithmetic overflow.
`TensorFill*` covers exact runtime fills and the existing Solve fill program
for zero/one initialization and AD seeds. The same counted writer proof handles
all helpers. Calls restore the saved caller scope and retain only heap effects;
the admitted fragment uses pure arguments and explicit void returns.
`CTensor.Lowering.emit_refines` composes these helpers for arbitrary prepared
programs, ranks and extents. The initial storage plan must provide disjoint
destinations and stable pointer/count bindings; the proof derives all later
register and storage invariants. It identifies the result buffer and preserves
the heap outside all destinations. Emission creates one call per instruction.
Allocation, nonfinite/error behavior, the outer ABI/linkage and FMI wrappers
remain separate obligations. No array source model gains production acceptance
from these theorems.
`lake run tensor-c-test` emits add/multiply/fill helpers and the existing
AD-generated square coefficient program in `build/tensor-c/`. It checks their
exact semantic certificates, rejects a changed helper bound and program
operator, and runs one native boundary check. The program fixture and its
fixed file adapter live in the separately named `TensorCChecks` library under
`Tests/`, keeping them out of runtime imports and avoiding shared `Tests.*`
module-path collisions. The full gate includes this artifact check.

`TreeLexical` and `Decimal` prepare certification of the general structured
printer: they prove identifier/natural token boundaries and independent numeric
values with canonical digits. This does not certify complete adapter expression
syntax, C integer type/range selection or a translation unit.

Run `lake build check-c` at the repository root for this package's cached
proof/audit library, or `lake test` in this package's own workspace. The full
source/artifact gate remains `nix develop .#verification --command lake test`
from the repository root. Native C compilation, the host ABI and hardware
remain outside the authored C/IEEE semantic boundary.
