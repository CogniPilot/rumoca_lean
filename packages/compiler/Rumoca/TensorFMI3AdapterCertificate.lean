import Rumoca.FMI3AdapterCertificate
import Rumoca.TensorProduction
import Rumoca.TensorAdapterChars
import RumocaFMI3.TensorAdapterContract
import RumocaFMI3.PublicAPICertificate

/-! Kernel certificate for the complete tensor adapter bytes, the tensor
instantiation of `Rumoca.FMI3AdapterCertificate.certifyAdapterBytes`. Candidate
signatures and rendered chunks have no proof authority: each chunk is checked
against its tensor function tree, their concatenation against the independently
read file, and the render-to-contract step is discharged by
`TensorAdapter.render_contract`. -/
namespace Rumoca.TensorFMI3AdapterCertificate
open Lean Elab Command
open Rumoca.FMI3AdapterCertificate (ProfileCertInputs certifyAdapterBytes)
open Rumoca.FMI3

/-- Emit the tensor adapter contract for the actual bytes. Returns the identifier
of a proof of
`∀ [static], TensorAdapter.Contract witnessModel Rumoca.squareModel (String.ofList actualChars)`
together with the reconstructed scalar witness artifact identifier. -/
def certify (adapter : String) (sigs : List CTree.Signature) (actualChars : Ident) :
    CommandElabM (Ident × Ident) := do
  let mTerm ← `(term| Rumoca.squareModel)
  let preambleTerm ← `(term|
    FMI3.functionPrefix ($mTerm).name ++ "#include \"model.c\"\n" ++
      FMI3.TensorStorage.declarations Rumoca.ArrayProfile.stateShape ($mTerm).hasOutput)
  certifyAdapterBytes {
    witnessName := "TensorSquare"
    witnessFile := "rumoca-tensor-witness:/scalar.mo"
    label := "tensor "
    base := `Rumoca.CheckedTensorFMI3Files.adapter
    mTerm := mTerm
    renderActual := fun wm ss => TensorFunctions.render wm Rumoca.squareModel ss
    functionsOf := fun wm ss => TensorFunctions.functions wm Rumoca.squareModel ss
    helpersCount := TensorFunctions.helpers.length
    helpersName := `Rumoca.FMI3.TensorFunctions.helpers
    functionName := `Rumoca.FMI3.TensorFunctions.tensorFunction
    functionsName := `Rumoca.FMI3.TensorFunctions.functions
    renderName := `Rumoca.FMI3.TensorFunctions.render
    adapterCharsLemma := `Rumoca.FMI3.TensorFunctions.tensor_adapter_chars
    preambleText :=
      functionPrefix Rumoca.squareModel.name ++ "#include \"model.c\"\n" ++
        TensorStorage.declarations Rumoca.ArrayProfile.stateShape Rumoca.squareModel.hasOutput
    preambleTerm := preambleTerm
    dischargeContract := fun ctx => do
      let ⟨contract, rendered, signatures, sigTerms, witnessModel, mTerm, actualChars, poolReady⟩ := ctx
      elabCommand (← `(command|
        theorem $contract:ident : ∀ [FMI3.StaticLiterals],
            FMI3.TensorAdapter.Contract $witnessModel $mTerm (String.ofList $actualChars) := by
          intro static
          rw [← $rendered:ident]
          refine FMI3.TensorAdapter.render_contract $witnessModel $mTerm $signatures ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · rw [FMI3.TensorFunctions.functions_names]; decide +kernel
          · change FMI3.StepEntry.signature ∈ [$sigTerms,*]
            simp [FMI3.StepEntry.signature]
          · change FMI3.PublicAPI.Covered [$sigTerms,*]
            fmi_public_coverage
          · intro ty write
            cases ty <;> cases write <;> change FMI3.AbsentVariables.signature _ _ ∈ [$sigTerms,*]
            all_goals simp [FMI3.AbsentVariables.signature, FMI3.AbsentVariables.VariableType.name,
              FMI3.AbsentVariables.VariableType.hasSizes]
          · change ∀ sig ∈ FMI3.CapabilityRejection.signatures, sig ∈ [$sigTerms,*]
            simp [FMI3.CapabilityRejection.signatures]
          · change ∀ sig ∈ [$sigTerms,*], sig.name ≠ "rumoca_rhs"
            decide +kernel
          · exact $poolReady:ident
          · change FMI3.DerivativeCalls.signature ∈ [$sigTerms,*]
            simp [FMI3.DerivativeCalls.signature]))
  } adapter sigs actualChars

end Rumoca.TensorFMI3AdapterCertificate
