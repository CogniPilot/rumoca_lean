import Rumoca.TensorEFMISourceMethod
import Rumoca.TensorEFMIFiniteJacobian
import RumocaEFMI.TensorStartup

/-! Source-bound execution products for the existing tensor eFMI slice.
Every inherited source/byte/XML/transport fact is retained. The method fields
refer to the same artifact and fixed function table; finite arithmetic and
symbolic allocated storage remain explicit preconditions. Actual publication
must require these products in its fixed checker, not merely import this file. -/
noncomputable section
namespace Rumoca
open EFMI ArrayProfile Tensor CMemory CMemory.TensorView CTensor Solve.Tensor
open EFMI.TensorProduction EFMI.TensorNumericalLinkage

/-- The complete ordinary methods, including the source-owned Jacobian, on the
same source and independently checked Algorithm/Production Code bytes. -/
structure TensorExecutedProductionContract (a : TensorArtifact source)
    (algorithm c : String) : Prop extends TensorProductionContract a algorithm c where
  /-- Finite RHS execution suffices; no independent Jacobian-addition premise. -/
  finiteSourceDoStep : SourceMethod.FiniteDoStep a c
  sourceDoStep (unusedKernel : CSyntax.Program)
      (values : String → Values stateShape) (objects : CDeclaredMembers.Objects)
      (heap : Heap) (base : Address) (rhs result : Values stateShape)
      (storage : TensorPublicStorage.Storage objects heap base
        (values a.prepared.parsed.parsed.ast.header.input))
      (rhsExecuted : Finite.Executes a.prepared.kernel.derivative
        (environment (values a.prepared.parsed.parsed.ast.header.state)
          (values a.prepared.parsed.parsed.ast.header.input)) rhs)
      (adds : ∀ i : Fin stateShape.volume,
        Binary64.Adds (values a.prepared.parsed.parsed.ast.header.input)[i]
          (values a.prepared.parsed.parsed.ast.header.input)[i] (.finite result[i])) :
      letI : CInterface := NumericalInterface.interface
      SourceObservation.SourceMatrix a values ∧
      c = "#include <stddef.h>\n#include <stdint.h>\n" ++
        String.join (numericalFunctions.map CTree.Function.render) ++
        TensorProduction.header ++ String.join (TensorProduction.functions.map CTree.Function.render) ∧
      ∃ diagonal : DiagonalProgram [stateShape, stateShape] stateShape,
        a.prepared.kernel.diagonal = some diagonal ∧
        ∃ finalHeap,
          ContextDoStep.Outcome objects heap finalHeap base
            (values a.prepared.parsed.parsed.ast.header.input) rhs result ∧
          Finite.Executes diagonal.coefficients
            (environment (values a.prepared.parsed.parsed.ast.header.state)
              (values a.prepared.parsed.parsed.ast.header.input)) result ∧
          Reads finalHeap (base.member jacobianVar.name)
            (diagonal.eval Finite.ops Binary64.positiveZero Binary64.one
              (environment (values a.prepared.parsed.parsed.ast.header.state)
                (values a.prepared.parsed.parsed.ast.header.input))) ∧
          SquareJacobianObservation.Observes finalHeap (base.member jacobianVar.name)
            (values a.prepared.parsed.parsed.ast.header.state)
            (values a.prepared.parsed.parsed.ast.header.input) ∧
          (∀ stack, Transition.Reaches
            (CContextMachine.machine (TensorContextCalls.expressions objects) (program unusedKernel)).step
            (.calling doStepName [.pointer (some base)] heap stack)
            (.returning (.integer 0) finalHeap stack)) ∧
          ∀ behavior,
            (CContextMachine.machine (TensorContextCalls.expressions objects) (program unusedKernel)).Behaves
              (.calling doStepName [.pointer (some base)] heap .done) behavior ↔
              behavior = .terminates ⟨.integer 0, finalHeap⟩
  allocatedStartup (unusedKernel : CSyntax.Program) (objects : CDeclaredMembers.Objects)
      (heap : Heap) (base : Address) (storage : TensorPublicStorage.AllocatedStorage objects heap base) :
      ∃ finalHeap, AllocatedMethods.StartupOutcome objects heap finalHeap base ∧
        AllocatedMethods.MethodResult unusedKernel objects startupName heap finalHeap base
  allocatedRecalibrate (unusedKernel : CSyntax.Program) (objects : CDeclaredMembers.Objects)
      (heap : Heap) (base : Address) (storage : TensorPublicStorage.AllocatedStorage objects heap base) :
      AllocatedMethods.RecalibrateOutcome objects heap (TensorPublicStorage.cleared heap base) base ∧
        AllocatedMethods.MethodResult unusedKernel objects recalibrateName heap
          (TensorPublicStorage.cleared heap base) base

theorem tensor_executed_production_correct (a : TensorArtifact source)
    (base : TensorProductionContract a algorithm c) :
    TensorExecutedProductionContract a algorithm c where
  toTensorProductionContract := base
  finiteSourceDoStep := SourceMethod.finiteDoStep a base
  sourceDoStep := SourceMethod.doStep a base
  allocatedStartup := AllocatedMethods.startup
  allocatedRecalibrate := AllocatedMethods.recalibrate

/-- XML facts and method execution share this artifact and these exact code bytes. -/
structure TensorExecutedManifestContract (a : TensorArtifact source) (identity : Manifest.Identity)
    (algorithm c algorithmXML productionXML contentXML : String) : Prop
    extends TensorManifestContract a identity algorithm c algorithmXML productionXML contentXML where
  execution : TensorExecutedProductionContract a algorithm c

theorem tensor_executed_manifests_correct (a : TensorArtifact source) (identity : Manifest.Identity)
    (base : TensorManifestContract a identity algorithm c algorithmXML productionXML contentXML) :
    TensorExecutedManifestContract a identity algorithm c algorithmXML productionXML contentXML where
  toTensorManifestContract := base
  execution := tensor_executed_production_correct a base.code

/-- One code witness carries both execution and exact archive transport.
The old contract remains available by projection; there is no second artifact
or unrelated byte witness for the new execution evidence. -/
def TensorExecutedArchiveContract (a : TensorArtifact source) (identity : Manifest.Identity)
    (bytes : ByteArray) : Prop :=
  ∃ code : Archive.Code,
    TensorExecutedManifestContract a identity code.algorithm code.production
      code.algorithmXML code.productionXML code.contentXML ∧
    StoredZIP.Format.Conforms (Archive.entries code) bytes

theorem tensor_executed_archive_correct (a : TensorArtifact source) (identity : Manifest.Identity)
    (code : Archive.Code)
    (manifests : TensorExecutedManifestContract a identity code.algorithm code.production
      code.algorithmXML code.productionXML code.contentXML)
    (transport : StoredZIP.Format.Conforms (Archive.entries code) bytes) :
    TensorExecutedArchiveContract a identity bytes := ⟨code, manifests, transport⟩

theorem TensorExecutedArchiveContract.toBase
    (contract : TensorExecutedArchiveContract a identity bytes) : TensorArchiveContract a identity bytes := by
  obtain ⟨code, manifests, transport⟩ := contract
  exact ⟨code, manifests.toTensorManifestContract, transport⟩

theorem TensorExecutedArchiveContract.code_members
    (contract : TensorExecutedArchiveContract a identity bytes) :
    ∃ code : Archive.Code,
      TensorExecutedManifestContract a identity code.algorithm code.production
        code.algorithmXML code.productionXML code.contentXML ∧
      ∀ member : Archive.Member,
        Archive.lookup (Archive.entries code) member.name = some (code.text member).toUTF8 ∧
        ∃ before after : List UInt8, bytes.data.toList = before ++
          StoredZIP.Format.localRecord ⟨member.name, (code.text member).toUTF8⟩ ++ after := by
  obtain ⟨code, manifests, transport⟩ := contract
  exact ⟨code, manifests, fun member => ⟨Archive.code_lookup code member,
    StoredZIP.Format.conforms_member transport (Archive.code_mem code member)⟩⟩

end Rumoca
