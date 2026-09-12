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
| `RuntimePrinter`, `AdapterPrinter` | Shared C grammar instantiation for every runtime body/helper and exact function-section binding with explicit typedef-name context |
| `CInterface` | FMI-specific constant and type bindings for shared C execution |
| `CallTypes` | Complete signature coverage, value-reference conversion and fresh typed entry for the rendered helper/API list; separate from body behavior and native ABI |
| `LiteralPreparation` | Literal collection and constructed definition table for the actual rendered function list; checked declaration block and all-observation pass preservation |
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
| `Reset`, `ResetCalls`, `ResetSyntax`, `ResetContract` | Default restoration, full typed calls, independent function syntax and the reset contract over the rendered definition table |
| `Package` | Native C compilation, FMU ZIP creation and independent validation |

C implementation and general target proofs live in `packages/backend-c` under
`RumocaC.*`; no compatibility copies remain here. XML syntax/rendering proofs
live in the independent XML package. Neither this package nor the shared C
backend imports the compiler driver or actual-file checker.

`LiteralPreparation.lowering_behaviors` derives collection, definition-table
coverage, structural call conditions and authored constant freshness from the
renderer's function list. It relates the original and named-literal versions
in the authored C machine, including stuck execution. The production renderer
does not yet use this pass. This theorem does not supply missing external-call,
callback, allocation, complete-header or whole-adapter byte semantics.

From the root inside `nix develop`, use `lake build check-fmi3` for cached
adapter proofs/audits and `lake build check-c` for shared C proofs/audits.
This package's `lake test` selects `RumocaFMI3Checks`.
`lake run fmi-test` runs the cross-package FMU/ABI checks; the required full
gate is `nix develop .#verification --command lake test`. The external native
compiler, object ABI and hardware remain outside the C semantic proof.
