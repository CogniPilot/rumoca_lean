# FMI 3 backend

This package owns the combined FMI 3 Model Exchange/Co-Simulation FMU:
public C interfaces, lifecycle adapters, model-specific XML and packaging.
It consumes the prepared numerical Solve product and uses the
[shared C backend](../backend-c/README.md) for numerical emission, structured
C construction, memory/call execution and certified numerical printing.

The path is DAE → Solve → C, wrapped by the FMI 3 interface. The C emitter
does not choose the solver or reconstruct source/DAE semantics. ME and CS
share the model kernel; the prepared integration policy supplies CS behavior.
The existing unit profile remains the admitted production path.

`RumocaFMI3.CInterface` supplies FMI constant and typedef bindings to shared
C execution. Each proof selects this dictionary locally; importing this package
does not install a global interpreter configuration. The adapter body theorems
cover state access, helper calls, derivatives, time, reference history and
successful initialization entry and exit for both ME and CS.
The complete printed ABI adapter and archive capstone remain open; see
[the FMI contracts](../../dev/fmi3/contracts.md).

| Modules | Responsibility |
| --- | --- |
| `Runtime`, `Header` | Structured FMI C bodies and signatures from the pinned official headers |
| `CInterface` | FMI-specific constant and type bindings for shared C execution |
| `Metadata` | Model-description XML projected from the prepared Solve model |
| `Identifier`, `IdentifierProofs` | Valid C identifiers, injective for distinct parsed model names |
| `BuildDescription`, `BuildDescriptionProofs` | Named single-translation-unit recipes, independent XML decoding and native argument requirements |
| `SourceLinkageProofs` | Certified source prefix/private-kernel include fragment and decoded ME/CS model identifiers |
| `GuardProofs`, `StateProofs` | Lifecycle predicates and generated state-access bodies |
| `LifecycleGuard` | Universal lifecycle guard/prefix execution in the shared C machine, preserving the heap |
| `LifecycleBodies` | Mode-write frames, complete successful termination and the error helper's terminating prefix |
| `CallProofs`, `DerivativeProofs` | Helper calls and the actual ME derivative body |
| `TimeProofs`, `HistoryProofs`, `HistoryBodies` | Binary64 time comparisons, reference history and generated history bodies |
| `InitializationBodies` | Successful ME/CS initialization exit, reference mode, model/history preservation and memory frame |
| `InitializationEntry` | Initialization argument validation, complete successful entry, stop/time-window representation and memory frame |
| `Package` | Native C compilation, FMU ZIP creation and independent validation |

C implementation and general target proofs live in `packages/backend-c` under
`RumocaC.*`; no compatibility copies remain here. XML syntax/rendering proofs
live in the independent XML package. Neither this package nor the shared C
backend imports the compiler driver or actual-file checker.

From the root inside `nix develop`, use `lake build check-fmi3` for cached
adapter proofs/audits and `lake build check-c` for shared C proofs/audits.
This package's `lake test` selects `RumocaFMI3Checks`.
`lake run fmi-test` runs the cross-package FMU/ABI checks; the required full
gate is `nix develop .#verification --command lake test`. The external native
compiler, object ABI and hardware remain outside the C semantic proof.
