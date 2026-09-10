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
| `Memory`, `Body`, `Calls` | Typed symbolic subobjects, small-step body execution and ordinary calls |
| `BooleanProofs` | Composition of Boolean-valued expressions using the existing short-circuit semantics |
| `Interface` | Explicit dictionary of header constant/type bindings |
| `Arithmetic` | Finite binary64 addition and multiplication for Solve expressions |
| `Algorithm` | Thin emission of prepared tensor Solve instructions |
| `LoopCode`, `Loops`, `LoopProofs` | Counted C loops, declared local types and compositional execution proofs |
| `TensorCode`, `TensorMemory`, `TensorProofs` | Shape-independent pointwise helpers, writable output ranges and complete body execution |
| `TensorSyntax`, `TensorContract`, `TensorArtifactCheck` | Independent helper token grammar, finite Solve/text contract and actual-file certificates |

`CInterface` is a parameter of the shared execution definitions. There is no
global default instance. Each adapter proof selects its dictionary locally;
FMI 3 names and eFMI header aliases belong to those adapters. There is one
implementation of the shared machine, with universal execution/lifting proofs.
Adapter body and actual-artifact contracts select the appropriate dictionary.

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

`CTensor.ArtifactContract` relates the complete actual helper text to the
independent finite Solve relation. Its conditions include readable finite
inputs, valid output storage and no arithmetic overflow. Whole-program
register allocation/calls, nonfinite/error behavior and FMI wrappers are
still separate obligations. No array source model gains production acceptance
from this helper theorem. `lake run tensor-c-test` emits the helper files in
`build/tensor-c/`, checks their exact semantic certificates, rejects a changed
loop bound and runs one native boundary check. The full gate includes it.

Run `lake build check-c` at the repository root for this package's cached
proof/audit library, or `lake test` in this package's own workspace. The full
source/artifact gate remains `nix develop .#verification --command lake test`
from the repository root. Native C compilation, the host ABI and hardware
remain outside the authored C/IEEE semantic boundary.
