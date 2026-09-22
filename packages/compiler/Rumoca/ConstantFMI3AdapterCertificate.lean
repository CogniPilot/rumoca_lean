import Rumoca.FMI3AdapterCertificate
import Rumoca.ConstantProduction
import Rumoca.ConstantAdapterChars
import RumocaFMI3.ConstantAdapterContract
import RumocaFMI3.PublicAPICertificate

/-! Kernel certificate for the complete constant-rate adapter bytes, the constant
instantiation of `Rumoca.FMI3AdapterCertificate.certifyAdapterBytes`. Candidate
signatures and rendered chunks have no proof authority: each chunk is checked
against its constant function tree, their concatenation against the independently
read file, and the render-to-contract step is discharged by
`ConstantAdapter.render_contract`. -/
namespace Rumoca.ConstantFMI3AdapterCertificate
open Lean Elab Command
open Rumoca.FMI3AdapterCertificate (ProfileCertInputs certifyAdapterBytes)
open Rumoca.FMI3

/-- Emit the constant adapter contract for the actual bytes. Returns the
identifier of a proof of
`∀ [static], ConstantAdapter.Contract witnessModel Rumoca.constantRatesModel (String.ofList actualChars)`
together with the reconstructed scalar witness artifact identifier. -/
def certify (adapter : String) (sigs : List CTree.Signature) (actualChars : Ident) :
    CommandElabM (Ident × Ident) := do
  let mTerm ← `(term| Rumoca.constantRatesModel)
  let preambleTerm ← `(term|
    FMI3.functionPrefix ($mTerm).name ++ "#include \"model.c\"\n" ++
      FMI3.ConstantFunctions.declarations ($mTerm).shape
        (FMI3.ConstantFunctions.rates $mTerm))
  certifyAdapterBytes {
    witnessName := "ConstantRates"
    witnessFile := "rumoca-constant-witness:/scalar.mo"
    label := "constant "
    base := `Rumoca.CheckedConstantFMI3Files.adapter
    mTerm := mTerm
    renderActual := fun wm ss => ConstantFunctions.render wm Rumoca.constantRatesModel ss
    functionsOf := fun wm ss => ConstantFunctions.functions wm Rumoca.constantRatesModel ss
    helpersCount := ConstantFunctions.helpers.length
    helpersName := `Rumoca.FMI3.ConstantFunctions.helpers
    functionName := `Rumoca.FMI3.ConstantFunctions.constantFunction
    functionsName := `Rumoca.FMI3.ConstantFunctions.functions
    renderName := `Rumoca.FMI3.ConstantFunctions.render
    adapterCharsLemma := `Rumoca.FMI3.ConstantFunctions.constant_adapter_chars
    preambleText :=
      functionPrefix Rumoca.constantRatesModel.name ++ "#include \"model.c\"\n" ++
        ConstantFunctions.declarations Rumoca.constantRatesModel.shape
          (ConstantFunctions.rates Rumoca.constantRatesModel)
    preambleTerm := preambleTerm
    dischargeContract := fun ctx => do
      let ⟨contract, rendered, signatures, sigTerms, witnessModel, mTerm, actualChars, poolReady⟩ := ctx
      elabCommand (← `(command|
        theorem $contract:ident : ∀ [FMI3.StaticLiterals],
            FMI3.ConstantAdapter.Contract $witnessModel $mTerm (String.ofList $actualChars) := by
          intro static
          rw [← $rendered:ident]
          refine FMI3.ConstantAdapter.render_contract $witnessModel $mTerm $signatures ?_ ?_ ?_ ?_ ?_ ?_
          · rw [FMI3.ConstantFunctions.functions_names]; decide +kernel
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
          · exact $poolReady:ident))
  } adapter sigs actualChars

end Rumoca.ConstantFMI3AdapterCertificate
