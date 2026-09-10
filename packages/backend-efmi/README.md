# Tiny eFMI backend

This package renders the checked GALEC Algorithm Code product and emits
Production C directly from its prepared Solve algorithm. DAE admission,
numerical policy and GALEC-to-Solve algorithm lowering belong to core/compiler.
The backend must consume those prepared products without repeating those phases.

Use `lake build check-efmi` from the repository root for incremental backend proofs
and axiom checks. `RumocaEFMIChecks` is the package's `lake test` library.
Actual source/code/manifest checks are separate: `lake run efmi-production-test`
runs the cross-package artifact boundary. See
[development commands](../../docs/development.md).

Generic checksum and XML tooling live in the independent
[sha1](../sha1/README.md) and [xml](../xml/README.md) packages. Their proofs and
audits run through `lake build check-sha1` and `lake build check-xml`; this backend owns
the eFMI manifest structure, logical mappings and reference graph.

The pinned authority is the official **eFMI 1.0.0 Beta 1** specification and its
accompanying schemas. This is a candidate draft, not a final 1.0.0 release.
See [the standard review and completion gates](../../dev/efmi.md).

`RumocaEFMI.AlgorithmProofs` checks that the emitted unit block parses through
the shared LALR engine, denotes the admitted named profile, and uses the CFG
processed from the actual embedded EBNF. The compiler composes those results
with the source/DAE and Solve refinement theorems. Its fixed actual-file adapter
reads both grammars, the Modelica input and the `.alg` member independently.

From the workspace, after building:

```sh
packages/compiler/.lake/build/bin/rumoca examples/Integrator.mo -o build/Integrator.alg
packages/compiler/.lake/build/bin/rumoca examples/Integrator.mo -o build/Integrator.efmu
```

These commands check the actual staged bytes in Lean before publishing the
Algorithm Code member or complete eFMU. The Production C path
has method execution, memory isolation, serial lifecycle trace and independent
structural C printer proofs, composed with the source theorem in the compiler package.
`Tools/CheckEFMIProduction.lean` checks the actual GALEC/C pair and both grammars.
Its C boundary is the authored finite binary64 object-memory semantics; host
scheduling, the physical ABI and subsequent native compilation remain explicit
assumptions. The actual manifest contract extends the code certificate;
the complete source-to-archive certificate additionally binds the ZIP bytes
and all pinned resources. That contract passed the full archive gate.
No full eFMI conformance or generic GALEC language coverage is claimed.

The interface declares `EfmiReal` (`double`) and `EfmiStatus` (`int32_t`);
every verified method returns status zero. The complete C contract also checks
these declarations and the logical variable/function mappings. The manifest
contract binds those mappings to the serialized XML. E05/E06 still require
review of the official checker/layout discrepancy before a release claim.

The emitter preserves each scalar Solve instruction as a declaration and
writes the returned value to the selected instance field. Unsupported tensor
storage is rejected without scalarization. The backend reuses C syntax trees,
typed memory and function-entry rules from backend-c; its arithmetic machine
adds the finite declaration-initializer addition needed by this profile.

The compiler's `rumoca verify-efmi INPUT --source MODEL.mo` command accepts a
complete archive or our prepared directory layout through `RumocaEFMI.Directory`: `__content.xml`,
`AlgorithmCode/{manifest.xml,model.alg}` and
`ProductionCode/{manifest.xml,production.c}`. IDs and the generation time come
from the actual manifest headers; no separate environment configuration is
needed. Candidate header extraction is only a file adapter. Full manifest
equality, XML correctness and the identity profile are kernel checked.
Archive checking uses the same in-memory code/XML snapshot and certifies the
complete stored-ZIP byte grammar. This command is for the frozen profile,
not a general eFMU importer.

The compiler supplies the parsed source model name separately from generated
code identifiers. `Manifest.prepare_named` preserves that name in all three
manifests. The compiler's `ManifestContract.source_name` relates the actual
XML strings to the source AST name through the checked XML syntax trees.

`Identity` defines the pinned schema's UUID layout and our whole-second UTC
profile. It checks the entire string, case-normalized ID distinctness, and a
valid Gregorian date using `Std.Time`. `IdentityProofs` connects the accepted
timestamp fields to a checked `PlainDate`. `ManifestProofs.prepare_identified`
binds the identity predicates to all three root attribute lists. Global UUID
freshness and the truth of an externally supplied generation time are separate
from these syntax/calendar guarantees.

`ZIPFormat`, `StoredZIP` and `ZIPProofs` provide the restricted stored ZIP32
transport for E05. Serialization has soundness and completeness
theorems for all admissible member sequences; parsing acceptance is checked
against the complete byte grammar. The compiler's `ArchiveContract` composes
these proofs with the manifest graph; its pure archive generator has a
preservation theorem. The combined actual-file gate passed in
`build/efmi-archive-full-gate.log`. The compiler's `.efmu` publisher invokes
that checker on the staged archive before renaming it. Validation of this
public path is recorded in `build/efmi-publication-full-gate.log`. General
correctness theorems take priority over adding example test matrices.

Run the complete repository gate with
`nix develop .#verification --command lake test`.

Production C consumes the checked GALEC-to-Solve refinement through the shared
[backend-c package](../backend-c/README.md). GALEC text and the C member have a
common checked GALEC origin; C generation reads the resulting Solve algorithm.
This package owns method interfaces, variable mappings, complete-function
printer proofs, manifests and packaging. `CInterface` derives real/status alias
bindings from the actual header declarations; `CHeader.interface_return`
connects those declarations to the shared C conversion for every value.
There is no dependency on the FMI 3 backend.
