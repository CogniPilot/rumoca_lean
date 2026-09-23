import RumocaCore.GALEC.Elaboration.Block.Headers
import RumocaCore.GALEC.Elaboration.Methods.Correspondence
import RumocaCore.GALEC.Elaboration.Capabilities.Initialization
import RumocaCore.GALEC.Elaboration.Capabilities.DoStep.Policy

/-! Compose the restricted three-method interface with original-body preparation.
All three methods come from one block. This is not lifecycle execution or full
normative permission checking. In particular the Startup input conflict remains.
-/
namespace Rumoca.GALEC.Elaboration.Block
open Elaboration Rumoca.Tensor Rumoca.Solve.Tensor

structure Result where
  interface : Headers.Interface
  startup : Methods.Preparation.Result
  recalibrate : Methods.Preparation.Result
  doStep : Methods.Preparation.Result

def fromBlock (ceiling : Nat) (block : AST.Block) : Option Result := do
  let interface ← Headers.read block
  let startup ← Methods.Preparation.fromBlock (.literal "Startup")
    Capabilities.Initialization.role ceiling block
  let recalibrate ← Methods.Preparation.fromBlock (.literal "Recalibrate")
    Capabilities.DoStep.role ceiling block
  let doStep ← Methods.Preparation.fromBlock (.literal "DoStep")
    Capabilities.DoStep.role ceiling block
  pure ⟨interface, startup, recalibrate, doStep⟩

structure Prepares (ceiling : Nat) (block : AST.Block) (result : Result) : Prop where
  headers : Headers.Valid block result.interface
  startup : Methods.Preparation.Prepares (.literal "Startup")
    Capabilities.Initialization.role ceiling block result.startup
  recalibrate : Methods.Preparation.Prepares (.literal "Recalibrate")
    Capabilities.DoStep.role ceiling block result.recalibrate
  doStep : Methods.Preparation.Prepares (.literal "DoStep")
    Capabilities.DoStep.role ceiling block result.doStep

theorem fromBlock_iff (ceiling : Nat) (block : AST.Block) (result : Result) :
    fromBlock ceiling block = some result ↔ Prepares ceiling block result := by
  constructor
  · intro found
    obtain ⟨interface, headers, remaining⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨startup, started, remaining⟩ := Option.bind_eq_some_iff.mp remaining
    obtain ⟨recalibrate, recalibrated, remaining⟩ := Option.bind_eq_some_iff.mp remaining
    obtain ⟨doStep, stepped, same⟩ := Option.bind_eq_some_iff.mp remaining
    cases Option.some.inj same
    exact ⟨(Headers.read_iff _ _).mp headers,
      (Methods.Preparation.fromBlock_iff _ _ _ _ _).mp started,
      (Methods.Preparation.fromBlock_iff _ _ _ _ _).mp recalibrated,
      (Methods.Preparation.fromBlock_iff _ _ _ _ _).mp stepped⟩
  · rintro ⟨headers, startup, recalibrate, doStep⟩
    simp only [fromBlock, (Headers.read_iff _ _).mpr headers,
      (Methods.Preparation.fromBlock_iff _ _ _ _ _).mpr startup,
      (Methods.Preparation.fromBlock_iff _ _ _ _ _).mpr recalibrate,
      (Methods.Preparation.fromBlock_iff _ _ _ _ _).mpr doStep]
    rfl

theorem all_metadata (prepared : Prepares ceiling block result) :
    result.startup.1.map Layout.Field.declaration = result.recalibrate.1.map Layout.Field.declaration ∧
    result.recalibrate.1.map Layout.Field.declaration = result.doStep.1.map Layout.Field.declaration :=
  ⟨Methods.Correspondence.prepared_metadata_eq prepared.startup prepared.recalibrate,
    Methods.Correspondence.prepared_metadata_eq prepared.recalibrate prepared.doStep⟩

theorem all_methods (prepared : Prepares ceiling block result)
    (member : method ∈ block.methods) :
    method = result.interface.startup ∨ method = result.interface.recalibrate ∨
      method = result.interface.doStep :=
  Headers.method_covered prepared.headers member

end Rumoca.GALEC.Elaboration.Block
