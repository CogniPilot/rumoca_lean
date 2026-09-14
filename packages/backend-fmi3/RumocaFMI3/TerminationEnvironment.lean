import RumocaFMI3.RuntimeEnvironment
import RumocaFMI3.TerminationRelease

noncomputable section
namespace Rumoca.FMI3.TerminationEnvironment
open CTree CMemory CBody StaticFactory CLiteral.Interface

theorem body_agrees (header : CFenv.Header) (model : Solve.FMI3Model source)
    (objects : Objects) (literals : CLiteralAddresses) :
    CodeAgrees (cInterface literals) (RuntimeEnvironment.interface header objects literals)
      (Runtime.body model Termination.signature) := by
  rw [Termination.body]
  simp [CodeAgrees, StmtAgrees, ExprAgrees, names, Runtime.require, Runtime.instancePrefix,
    Runtime.modeGuard, Runtime.allowedExpression, permittedModes, Runtime.put,
    Runtime.setMode, Runtime.mode, Runtime.ok, Runtime.reject, Runtime.fail,
    Runtime.branch, Runtime.ret, Runtime.any, Runtime.both, Runtime.either,
    Runtime.negate, Runtime.eqv, Runtime.field, Runtime.call, Runtime.v, Runtime.n,
    Expr.nullPointer, RuntimeEnvironment.interface, CFenv.Header.interface,
    CInterface.constants, objectConstants]

/-- Complete successful/null termination in the same header/object/literal
interface as CS stepping. The original finite-body proof supplies execution. -/
theorem quiet_correct {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E),
      program.internal.definitions Termination.signature.name =
        some (.tree (Runtime.function model Termination.signature)) →
      Termination.QuietContract program := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program defined
  constructor
  · intro heap p kind mode kindValue modeValue allowed behavior
    have executed := LifecycleBodies.terminate_run (static := ⟨literals⟩) model Termination.signature rfl
      heap p kind mode kindValue modeValue allowed
    exact CCalls.Events.body_call_interface_behaviors (cInterface literals)
      (RuntimeEnvironment.interface header objects literals) (RuntimeEnvironment.types_agree header objects literals) rfl
      program (Runtime.function model Termination.signature) _ _ heap _ (.integer 0) 5
      defined rfl (Termination.closed model) (body_agrees header model objects literals) executed rfl behavior
  · intro heap behavior
    let rest := [Runtime.modeGuard .terminate, Runtime.setMode .terminated, Runtime.ok]
    have executed := GuardedCalls.null_body (static := ⟨literals⟩) StateProofs.nullParameters heap rest
      (by simp [StateProofs.nullParameters]) (by simp [StateProofs.nullParameters]) (by simp [StateProofs.nullParameters])
    have body : (Runtime.function model Termination.signature).body = Runtime.instancePrefix ++ rest := by
      simp [Runtime.function, Termination.body, Runtime.require, rest, List.append_assoc]
    rw [← body] at executed
    exact CCalls.Events.body_call_interface_behaviors (cInterface literals)
      (RuntimeEnvironment.interface header objects literals) (RuntimeEnvironment.types_agree header objects literals) rfl
      program (Runtime.function model Termination.signature) _ _ heap _ (.integer 3) 3
      defined rfl (Termination.closed model) (body_agrees header model objects literals) executed rfl behavior

/-- Termination and release preserve the same original lease assumptions;
termination derives the metadata/ownership used by the actual atomic release. -/
theorem release_correct {E : Type} (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E),
      Termination.QuietContract program → StaticRelease.Bindings program tag →
      Termination.ReleaseContract objects program tag := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program tag quiet bindings heap slot owners owner kind mode
  let p := objects.instances.index slot.val
  dsimp only
  intro kindValue modeValue allowed represented owned metadata
  obtain ⟨discharged, representedAfter, _, framed, freed⟩ := StaticRelease.release_owned program tag
    (LifecycleBodies.writeMode heap p .terminated) objects.instances objects.flagsBlock owners slot owner bindings rfl
    (Termination.lease_owners objects heap slot owners represented) owned
    ((Termination.lease_metadata heap p).trans metadata)
  refine ⟨quiet.successful heap p kind mode kindValue modeValue allowed,
    discharged, representedAfter, ?_, freed⟩
  intro query outsideMode outsideFlag
  exact (framed query outsideFlag).trans (LifecycleBodies.write_frame heap p query .terminated outsideMode)

end Rumoca.FMI3.TerminationEnvironment
end
