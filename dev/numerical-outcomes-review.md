# Numerical outcomes and error detection — 2026-09-22

Status: **open; blocks grammar growth**. This focused follow-up reviews the
existing tensor profile at `20d6da9`, not a new language case or a completed
three-standard stage review. Compiler semantics, admission and artifacts are
unchanged. The previous full gate remains evidence for its stated finite-source
and total-helper contracts, not for MISRA compliance.

## Normative distinction

- eFMI 1.0.0 Beta 1 §3.2.5 §2 assumes a processor configured for nontrapping
  signed-infinity results on ordinary Real overflow and quiet-NaN propagation.
  This is a target-environment obligation, not an unconditional host guarantee.
  It separately specifies
  `NAN` signaling for relational operations with NaN operands. Ordinary Real
  multiplication overflow is not specified there as an automatic `OVERFLOW`
  signal. §3.2.5 §1.3 relates a method's exposed signals to its reachable
  signals; §1.6 assigns bit 1 to an exposed `OVERFLOW` signal. Therefore adding
  that bit only in Production C, without a matching Algorithm Code contract,
  is not a lowering repair justified by the cited GALEC contract. This is an interpretation of the
  [pinned text](https://www.efmi-standard.org/media/home/eFMI-Standard-1.0.0-Beta-1.html#_2_and_quiet_not_a_number_propagation),
  not a Lean conformance theorem.
- MISRA C:2025 **Dir 4.15, Required**, printed pp. 32–33, requires detection of
  potentially generated infinities/NaNs. Delayed detection needs an argument
  that propagation cannot reach code unprepared for such values. An IEEE result
  proof or a finite-input assumption alone does not discharge this directive:
  finite operands can overflow. The user's PDF is the authority, not the
  previous ledger paraphrase. No deviation or integration restriction is
  approved by this review.
- FMI 3.0.2 §2.2.4 distinguishes recoverable `fmi3Discard` (instance state
  unchanged) from `fmi3Error`; §2.2.7.3 discusses range violations. The note
  for `fmi3GetContinuousStateDerivatives` in §3.2.1 recommends `fmi3Discard`
  for numerical evaluation failure. This does not establish a universal
  overflow-to-status rule for both ME and CS. Any selected policy must prove
  its state, outputs and logging behavior at the actual entry point.
  [FMI status requirements](https://fmi-standard.org/docs/3.0.2/#status-returned-by-functions).
- MLS 3.7 coverage and the explicit `jacobian` extension remain as previously
  reviewed. No new MLS overflow interpretation is adopted. The exact real RHS
  and its mathematical derivative must remain distinct from encoded numerical
  outcomes; infinity is not a real-valued derivative witness.

## Concrete finding N01: tensor eFMI has no output exception detection

The actual `ProductionCode/production.c` sets `errorSignalStatus` to zero on
line 89, calls the square RHS and diagonal Jacobian on lines 90–91, and returns
the unchanged word on line 92. There is no exceptional-value detection in that
translation unit. `AlgorithmCode/model.alg` has no signal interface or explicit
error handling. These correspond to `TensorProductionCode.lean`'s `method` and
`doStepFunction`, and `TensorAlgorithmCode.lean`'s `tensorUnitSource`.

A one-off native observation on freshly extracted bytes initialized `Model`
with zeroed storage, selected `FE_TONEAREST`, called Startup, set
`u = {DBL_MAX, -DBL_MAX}`, then called DoStep. It printed:

```text
status=0 stored=0 x=(inf,inf) J=(inf,0x0p+0,0x0p+0,-inf)
```

GCC 15.2.0 compilation used the existing native boundary's flags: C11, `-O2 -Wall -Wextra
-Werror -Wno-unused-parameter -fno-fast-math -ffp-contract=off -frounding-math`,
linked with `-lm`. The initial diagnostic omitted `-Wno-unused-parameter` and
failed on the existing unused RHS state parameter; rerunning with the existing
boundary's flags passed. No generated source was edited. This is host behavior,
not a new regression acceptance criterion, native correspondence proof, or proof
that eFMI mandates a nonzero result here.

The finding is a missing **MISRA detection/integration argument** at the public
output boundary. No runtime detection or proved host-side delayed-detection
contract currently accompanies these exceptional outputs. The present finite
source DoStep theorem excludes this input through its finite-square premise;
the newer total helper theorems deliberately do not close this gap.
Specifically, `SourceMethod.FiniteDoStep` in
`packages/compiler/Rumoca/TensorEFMIFiniteJacobian.lean` requires
`Finite.Executes` for the prepared derivative, and
`TensorExecutedProductionContract.finiteSourceDoStep` requires that proposition.

To reproduce the observation after extracting the hashed eFMU to a scratch
directory, compile a separate translation unit including `<fenv.h>`,
`<float.h>`, `<inttypes.h>`, `<stdio.h>` and the extracted
`ProductionCode/production.c`, with this diagnostic body and the flags above:

```c
int main(void) {
  Model model = {0};
  if (fesetround(FE_TONEAREST) != 0) { return 1; }
  if (TensorSquare_Startup(&model) != 0) { return 2; }
  model.u[0] = DBL_MAX;
  model.u[1] = -DBL_MAX;
  const int32_t status = TensorSquare_DoStep(&model);
  printf("status=%" PRId32 " stored=%" PRId32 " x=(%a,%a) J=(%a,%a,%a,%a)\n",
         status, model.errorSignalStatus, model.x[0], model.x[1],
         model.J[0], model.J[1], model.J[2], model.J[3]);
  return 0;
}
```

## Closure criteria and next implementation

Read-only product preflight now has owner-checked Lean proofs and an actual-file
contract (`RumocaC.TensorProductPreflightContract`). It computes into one scalar
local, classifies the product immediately, and returns Solve's exact finiteness
decision with the entire heap unchanged. This is needed to preserve FMI instance
state on numerical Discard without tightening existing caller-buffer aliasing
premises. Public-method invocation, logging/status behavior and production
artifact linkage remain to be implemented; N01 is not closed. The required full
gate passed (exit 0, observed 2026-09-22 at 11:09 UTC), with 2,464 frozen inputs,
7,711 permitted printed axiom reports, all 14 new roots and four retained FMU
roots checked. Existing actual-helper/native/mutation and FMI/eFMI checks passed;
bounded independent review found no issue. See `build/tensor-preflight-full-gate-v1.log`.
The scalar initializer is not itself a dead-code candidate under MISRA C:2025
Rule 2.2, Notes 3 (printed p. 43); this narrow check does not close the other
coding-guideline or integration obligations.

1. Specify numerical outcomes and detection in the prepared Solve/algorithm
   contract, retaining tensor shape and the independent real refinement on
   successful finite results. Do not weaken finite contracts or reinterpret
   infinity as mathematical success.
2. Establish a coherent detection boundary for the existing profile. If exposed
   eFMI signals are chosen, their GALEC semantics, signal interface, Production C
   status and actual manifests must agree; a backend-only status patch is not
   sufficient. Any delayed host detection needs an explicit integration contract
   and evidence, not an invented host assumption. Cover every potentially
   generated infinity/NaN path in the admitted profile, identify all downstream
   consumers, and prove each consumer before detection is prepared to handle
   those values. Sampling a few exceptional outcomes cannot close Dir 4.15.
3. Specify FMI ME/CS numerical failure separately, including restoration/frame
   requirements for Discard. Preserve ownership: Solve provides the executable
   numerical outcome, while the interfaces encode their own failure protocols.
4. Prove source/lowering/target/actual-artifact correspondence, audit the new
   roots, and extend the existing native boundary checks for selected outcomes.
   Run the required full `nix develop .#verification --command lake test` gate.
   No grammar expansion, MISRA closure or full public-overflow claim precedes
   resolution of this and the other open stage findings.

## Evidence identities

SHA-256 identities rechecked during this review:

| Evidence | SHA-256 |
| --- | --- |
| User MISRA C:2025 PDF | `42d1f700d83506566964131c6b618f4eba14782ea8fa7b7355924bb7c4b882aa` |
| Official eFMI Beta 1 release ZIP | `da5caf207aca412b5601cafaaf72d4e613d1c78964e3f39afc6a5a3d06281a89` |
| `build/TensorSquare.efmu` | `dea1fe44c26629b27d292edc6e22d8384222a8d7ffc213089e01b52216cb1ed7` |
| Its `ProductionCode/production.c` | `584e58f60fff3a97b29bf8f5b7e3b77eed5da348e759aea060aa1822928bc8b4` |
| Its `AlgorithmCode/model.alg` | `08bc50315b24a74517aa979c4a80b6f176b7b787d4656d669520b583674c106d` |

The local eFMI HTML was byte-compared with its member in the pinned release ZIP.
Dir 4.15 was freshly extracted from the hashed user PDF with `pdftotext`; no
normative PDF is redistributed. The native observation used a temporary
extraction and diagnostic, not a rebuilt or republished eFMU. This documentation-
only review does not rerun or claim a new full artifact gate.
A bounded independent documentation review confirmed the normative distinction
and requested the target-configuration and all-path detection qualifications
above. This is not independent MISRA compliance sign-off.
