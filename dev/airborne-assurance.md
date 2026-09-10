# Airborne software assurance readiness

Status: 2026-09-10. This is an engineering gap plan, not a DO-178C compliance
finding, tool qualification package, or certification authority agreement.
The kernel and FMI/eFMI work remain incomplete under [verification.md](../docs/verification.md).
The intended target is a core that can support a serious airborne software
assurance project without redesigning its evidence and provenance mechanisms.

## Applicable framework

FAA [AC 20-115D](https://www.faa.gov/documentLibrary/media/Advisory_Circular/AC_20-115D.pdf)
recognizes DO-178C and its applicable supplements as an acceptable means of
compliance. Its §§6, 8 and 10 address lifecycle evidence, supplement use and
tool qualification. The software level follows the system safety assessment;
carrying humans does not by itself assign a level to every component.
A compiler preservation theorem alone does not satisfy the applicable
objectives for an aircraft installation.

[RTCA's overview](https://www.rtca.org/do-178/) identifies DO-333 for formal
methods, DO-331 for model-based development and DO-330 for tool qualification.
We need a project-specific strategy for credit from proofs and generator or
checker tools. A translation validator can change the trust analysis; it does
not automatically eliminate tool qualification or all testing obligations.
The full licensed standards and applicable objective tables have not been
reviewed here. Do not treat this plan as a complete Annex A assessment or
assign a tool qualification level from it.

## Project gaps and acceptance evidence

| ID | Gap | Evidence required to close it |
| --- | --- | --- |
| AIR01 | Safety allocation and assurance plans | Identified aircraft function, failure conditions, assigned software level, agreed plans and review responsibilities |
| AIR02 | Validated requirements | Reviewed source-language, numerical, solver, lifecycle, timing and target-environment requirements with stable identifiers |
| AIR03 | Bidirectional traceability | Requirements ↔ architecture/implementation ↔ theorem statements/proofs ↔ necessary tests; impact analysis and explicit treatment of derived requirements |
| AIR04 | Source provenance | The [provenance gates](provenance.md), including IR origins and actual generated-member maps; not just parser token spans |
| AIR05 | Formal-methods evidence | Independent review of specification adequacy, theorem scope, assumptions, non-vacuity, domains, refinement composition and exact artifact binding |
| AIR06 | Remaining compiler/runtime contracts | Closure of the main FMI/eFMI roadmap, generic parser gaps, adapter text/execution binding, invalid calls, external observations and lifetime obligations |
| AIR07 | Executable target assurance | Defined C compiler/options, ABI, FPU behavior, linker/runtime/library assumptions and an accepted object-code verification strategy on the target |
| AIR08 | Embedded integration | Explicit resource, memory, stack, execution-time, scheduling, initialization and fault-handling contracts; integration evidence for the actual system |
| AIR09 | Tool-credit strategy | Intended use and impact analysis for compiler, proof checker, file adapters, build tools and downstream compilation; qualification plans/evidence where required |
| AIR10 | Controlled lifecycle | Reproducible baselines, configuration management, problem/change records, quality assurance, independent verification where applicable, and certification liaison records |

All AIR items remain open. Existing proofs and reproducible artifact checks
are inputs to these records, not substitutes for reviewed requirements or
independence. Do not manufacture historical review approvals or label the
present self-review independent.

The recommended endpoint remains prepared Solve IR → production C, followed
by a separately controlled C-to-machine toolchain. An assembly backend would
create additional proof and qualification obligations; it would not remove
these lifecycle gaps. A composed machine-code theorem could strengthen AIR07,
but the current generated-C theorem does not provide it.

Immediate sequencing: finish the small core's open semantic/artifact contracts,
preserve locations and origins through the existing IRs, attach stable
requirements identifiers to those contracts, and establish a reviewed
assurance/qualification strategy before representing the product as suitable
for flight-critical deployment. This does not authorize language expansion.
