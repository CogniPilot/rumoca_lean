import Rumoca.TensorEFMISourceMethod
import Rumoca.TensorEFMIFiniteJacobian
import RumocaC.TensorSquareDiagonalTotalContract
import RumocaC.TensorMultiplicationTotalContract
import RumocaEFMI.TensorContextRhsTotal
import RumocaEFMI.TensorStartup
import RumocaEFMI.TensorSourceMethods

/-! Source-bound execution products for the existing tensor eFMI slice.
Every inherited source/byte/XML/transport fact is retained. The method fields
refer to the same artifact and fixed function table; finite arithmetic and
symbolic allocated storage remain explicit preconditions. Actual publication
must require these products in its fixed checker, not merely import this file. -/
noncomputable section
namespace Rumoca
open EFMI ArrayProfile Tensor CMemory CMemory.TensorView CTensor Solve.Tensor
open EFMI.TensorProduction EFMI.TensorNumericalLinkage

/-! ### DoStep aligned with the Modelica source

The GALEC `x` output is an RHS buffer and is not equated to the Modelica state.
All tensor values and updates remain whole-shaped; this is single-call
semantics, not solver-state integration or a lifecycle. -/

section Alignment
open GALEC GALEC.Elaboration GALEC.Coefficients GALEC.VectorBodies TensorSourceMethods TensorAlgorithm

/-- The source DoStep post-store for a right-hand side `rhs`. -/
def AlignedStep.updated (input : InputEnv) (before : OutputEnv) (rhs : Values stateShape) :
    OutputEnv :=
  Env.update (Env.update @before (Square.squareRhs squareExtent) rhs) (Square.squareJacobian squareExtent)
    (diagonalValue Finite.ops Binary64.positiveZero Binary64.one doubledInput
      (input (Square.squareInput squareExtent)))

/-- Original method execution has exactly the prepared Modelica derivative's
finite domain and whole-store result, after aligning the shared input. -/
theorem AlignedStep.source_iff {block : AST.Block} {method : AST.Method}
    (a : TensorArtifact source) (model : TensorModel stateShape)
    (sameKernel : model.kernel = a.prepared.kernel)
    (semantics : StepSemantics squareExtent ceiling block method model.kernel)
    (values : String → Values stateShape) (input : InputEnv) (env : IteratorEnv [])
    (before after : OutputEnv)
    (aligned : input (Square.squareInput squareExtent) = values a.prepared.parsed.parsed.ast.header.input) :
    SourceExec (Square.squareFields squareExtent) ceiling block method Finite.Result
      Binary64.positiveZero Binary64.one @input @env @before @after ↔
      ∃ rhs, Finite.Executes a.prepared.kernel.derivative
        (environment (values a.prepared.parsed.parsed.ast.header.state)
          (values a.prepared.parsed.parsed.ast.header.input)) rhs ∧
        @after = @AlignedStep.updated @input @before rhs := by
  unfold AlignedStep.updated
  simpa only [sameKernel, aligned] using
    semantics (values a.prepared.parsed.parsed.ast.header.state) @input @env @before @after

/-- Exact behavior equivalence already determines the entire returned heap. -/
theorem AlignedStep.completed_heap_unique
    (first : ContextMethod.Completes p objects name heap left base)
    (second : ContextMethod.Completes p objects name heap right base) : left = right := by
  have same := (second.2 _).mp ((first.2 _).mpr rfl)
  cases same
  rfl

/-- The Modelica source observations of the public DoStep at a specified final
heap, retaining every source-method field. -/
def AlignedStep.ModelicaAt (a : TensorArtifact source) (c : String) (unusedKernel : CSyntax.Program)
    (values : String → Values stateShape) (objects : CDeclaredMembers.Objects)
    (heap finalHeap : Heap) (base : Address) (rhs result : Values stateShape) : Prop :=
  SourceObservation.SourceMatrix a values ∧
  c = "#include <stddef.h>\n#include <stdint.h>\n" ++
    String.join (numericalFunctions.map CTree.Function.render) ++
    TensorProduction.header ++ String.join (TensorProduction.functions.map CTree.Function.render) ∧
  ∃ diagonal : DiagonalProgram [stateShape, stateShape] stateShape,
    a.prepared.kernel.diagonal = some diagonal ∧
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
    ContextMethod.Completes (program unusedKernel) objects doStepName heap finalHeap base

/-- A single original DoStep method is fixed before all runtime environments.
Finite original RHS execution constructs the GALEC source result and both
source views of one public C execution, including all four logical fields. -/
def AlignedStep (a : TensorArtifact source) (model : TensorModel stateShape)
    (algorithm c : String) : Prop :=
  ∃ product method,
    Block.fromSource algorithm = .ok product ∧
    SourceContract squareExtent Static.Bounded.integerCeiling product.parsed.ast model.kernel ∧
    Methods.Headers.Selects (.ident "DoStep") product.parsed.ast.methods method ∧
    ∀ (unusedKernel : CSyntax.Program) (values : String → Values stateShape)
      (objects : CDeclaredMembers.Objects) (heap : Heap) (base : Address)
      (input : InputEnv) (env : IteratorEnv []) (before : OutputEnv) (rhs : Values stateShape),
      input (Square.squareInput squareExtent) = values a.prepared.parsed.parsed.ast.header.input →
      TensorPublicStorage.Storage objects heap base (values a.prepared.parsed.parsed.ast.header.input) →
      Reads heap (base.member GALEC.Names.clock) (input periodRef) →
      Finite.Executes a.prepared.kernel.derivative
        (environment (values a.prepared.parsed.parsed.ast.header.state)
          (values a.prepared.parsed.parsed.ast.header.input)) rhs →
      ∃ finalHeap,
        SourceExec (Square.squareFields squareExtent) Static.Bounded.integerCeiling
          product.parsed.ast method Finite.Result Binary64.positiveZero Binary64.one
          @input @env @before (@AlignedStep.updated @input @before rhs) ∧
        StateView finalHeap base @input (@AlignedStep.updated @input @before rhs) ∧
        AlignedStep.ModelicaAt a c unusedKernel values objects heap finalHeap base rhs
          ((squareJacobianProgram stateShape).coefficients.eval Finite.ops
            Binary64.positiveZero Binary64.one
            (environment (values a.prepared.parsed.parsed.ast.header.state)
              (values a.prepared.parsed.parsed.ast.header.input)))

theorem aligned_step (a : TensorArtifact source)
    (algorithmContract : TensorAlgorithmContract a algorithm)
    (finite : SourceMethod.FiniteDoStep a c) :
    AlignedStep a algorithmContract.model algorithm c := by
  obtain ⟨product, parsed, sourceContract⟩ := algorithmContract.source.original_source
  obtain ⟨startup, recalibrate, method, _, _, selected, _, _, semantics, _⟩ := sourceContract.original
  refine ⟨product, method, parsed, sourceContract, selected, ?_⟩
  intro unusedKernel values objects heap base input env before rhs aligned storage period finiteRhs
  have sourceRan := (AlignedStep.source_iff a algorithmContract.model rfl semantics
    values @input @env @before (@AlignedStep.updated @input @before rhs) aligned).mpr
      ⟨rhs, finiteRhs, rfl⟩
  have inputStorage : TensorPublicStorage.Storage objects heap base
      (input (Square.squareInput squareExtent)) := aligned.symm ▸ storage
  obtain ⟨finalHeap, _, view, completed⟩ := original_step sourceContract selected
    unusedKernel objects heap base @input @env @before (@AlignedStep.updated @input @before rhs)
    inputStorage period sourceRan
  obtain ⟨sourceMatrix, bytes, diagonal, index, other, outcome, executed, reads, math, ran, behaves⟩ :=
    finite unusedKernel values objects heap base rhs storage finiteRhs
  have same := AlignedStep.completed_heap_unique ⟨ran, behaves⟩ completed
  subst other
  exact ⟨finalHeap, sourceRan, view, sourceMatrix, bytes, diagonal, index, outcome, executed, reads,
    math, completed⟩

end Alignment

/-- The complete ordinary methods, including the source-owned Jacobian, on the
same source and independently checked Algorithm/Production Code bytes. -/
structure TensorExecutedProductionContract (a : TensorArtifact source)
    (algorithm c : String) : Prop extends TensorProductionContract a algorithm c where
  /-- Finite RHS execution suffices; no independent Jacobian-addition premise. -/
  finiteSourceDoStep : SourceMethod.FiniteDoStep a c
  /-- Total encoded helper outcomes, including overflow; all old finite public
  method and source derivative contracts remain separate and unchanged. -/
  jacobianOutcomes :
    c = "#include <stddef.h>\n#include <stdint.h>\n" ++
      String.join (numericalFunctions.map CTree.Function.render) ++
      TensorProduction.header ++ String.join (TensorProduction.functions.map CTree.Function.render) ∧
    CTensor.SquareDiagonal.Total.ArtifactContract CTensor.SquareDiagonal.function.render
  /-- Same actual C table, with total finite-input multiplication outcomes.
  This is not a source/public-method overflow theorem. -/
  multiplicationOutcomes :
    c = "#include <stddef.h>\n#include <stdint.h>\n" ++
      String.join (numericalFunctions.map CTree.Function.render) ++
      TensorProduction.header ++ String.join (TensorProduction.functions.map CTree.Function.render) ∧
    CTensor.MultiplicationTotal.ArtifactContract (CTensor.function .mul).render
  /-- Total prepared RHS execution in the same actual eFMI tables; finite
  source refinement is retained and infinity is never a real derivative. -/
  rhsOutcomes :
    c = "#include <stddef.h>\n#include <stdint.h>\n" ++
      String.join (numericalFunctions.map CTree.Function.render) ++
      TensorProduction.header ++ String.join (TensorProduction.functions.map CTree.Function.render) ∧
    CTensor.SquareRhsTotal.ArtifactContract CTensor.ProgramFixture.IVPEntry.sources.derivative ∧
    CTensor.SquareRhsTotal.LinkedArtifactContract c numericalFunctions
      "#include <stddef.h>\n#include <stdint.h>\n"
      (TensorProduction.header ++ String.join (TensorProduction.functions.map CTree.Function.render)) ∧
    ContextRhsTotal.CallContract
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
  /-- All three original Algorithm Code methods correspond to the public calls on
  these same Algorithm and Production C bytes. -/
  methods : TensorSourceMethods.MethodsContract algorithm_contract.model algorithm c
  /-- One original DoStep execution, aligned with the Modelica input, and one
  public call share a final heap and all source observations. -/
  aligned : AlignedStep a algorithm_contract.model algorithm c

theorem tensor_executed_production_correct (a : TensorArtifact source)
    (base : TensorProductionContract a algorithm c) :
    TensorExecutedProductionContract a algorithm c where
  toTensorProductionContract := base
  finiteSourceDoStep := SourceMethod.finiteDoStep a base
  jacobianOutcomes := ⟨JacobianObservation.actual_trees a base,
    CTensor.SquareDiagonal.Total.artifact_correct _ rfl⟩
  multiplicationOutcomes := ⟨JacobianObservation.actual_trees a base,
    CTensor.MultiplicationTotal.artifact_correct _ rfl⟩
  rhsOutcomes := ⟨JacobianObservation.actual_trees a base,
    CTensor.SquareRhsTotal.artifact_correct _ rfl,
    CTensor.SquareRhsTotal.linked_artifact_correct c numericalFunctions _ _
      (by simpa only [String.append_assoc] using JacobianObservation.actual_trees a base)
      ContextRhsTotal.storage,
    ContextRhsTotal.call_correct⟩
  sourceDoStep := SourceMethod.doStep a base
  allocatedStartup := AllocatedMethods.startup
  allocatedRecalibrate := AllocatedMethods.recalibrate
  methods := TensorSourceMethods.methods_correct base.algorithm_contract.source base.code
  aligned := aligned_step a base.algorithm_contract (SourceMethod.finiteDoStep a base)

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
