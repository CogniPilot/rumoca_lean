import RumocaC.Initialization
import RumocaC.OriginProofs
import RumocaCore.Provenance.Lowering

/-! The actual C initialization statement preserves both its execution
contract and exact operation/operand origins. Storage, ABI and actual enclosing
file/map correspondence remain separate requirements. -/
namespace Rumoca.CInitialization
open CTree CMemory
open _root_.Parser.Provenance (Ref Node TracesTo)

def ValueOriginsCorrect (model : Solve.Model source)
    {table : CProvenance.Table model.dae.flat.context} : Expr.Origins table (value model) → Prop
  | .cast operation typeName (.nat literal) =>
      table.get literal = .generated .initialLiteral model.origins.completion.index.val #[] ∧
      table.get operation = .derived .initialConversion literal.index.val
        #[(model.sourceOrigin .declaration).index.val] ∧ typeName = operation

/-- Inspect the annotations actually attached to the cast/literal and every
node of the target expression. The write's parents are these actual roots. -/
def Emission.TraceCorrect (emission : Emission model target) : Prop :=
  ValueOriginsCorrect model emission.valueOrigins ∧
  emission.targetOrigins.Every (fun ref => emission.origins.table.get ref =
    .generated .stateStorage (model.sourceOrigin .stateName).index.val
      #[(model.sourceOrigin .declaration).index.val]) ∧
  emission.origins.table.get emission.origins.write =
    .generated .initializeState model.origins.completion.index.val
      #[emission.valueOrigins.root.index.val, emission.targetOrigins.root.index.val]

theorem Emission.trace_correct (emission : Emission model target) : emission.TraceCorrect := by
  refine ⟨?_, ?_, ?_⟩
  · rw [emission.value_checked]
    exact ⟨emission.origins.literal_correct, emission.origins.conversion_correct, rfl⟩
  · apply emission.targetOrigins.every_mono _ _ _ emission.target_checked
    intro ref same
    rw [same]
    exact emission.origins.target_correct
  · have targetRoot := emission.targetOrigins.every_root _ emission.target_checked
    rw [emission.value_checked, targetRoot]
    exact emission.origins.write_correct

theorem emit_trace_correct (model : Solve.Model source) (target : Expr) :
    (emit model target).TraceCorrect := (emit model target).trace_correct

private def Origins.fromSolve (origins : Origins model) (ref : Ref model.origins.table) :
    Ref origins.table :=
  origins.extension.ref (model.origins.table.mapRef CProvenance.Rule.upstream ref)

private theorem Origins.fromSolve_trace (origins : Origins model) (ref : Ref model.origins.table)
    (site : _root_.Parser.Provenance.SourceRef model.dae.flat.context.input.inputs)
    (trace : TracesTo model.origins.table ref site) :
    TracesTo origins.table (origins.fromSolve ref) site :=
  (trace.mapRule CProvenance.Rule.upstream).extend origins.extension

theorem Origins.initial_ancestry (origins : Origins model) :
    TracesTo origins.table origins.literal (model.dae.flat.context.site .declaration) := by
  apply TracesTo.parent (parent := origins.fromSolve model.origins.completion)
    _ (origins.fromSolve_trace _ _ model.completion_ancestry)
  rw [origins.literal_correct]
  simp [Node.parents, fromSolve, _root_.Parser.Provenance.Table.Extension.ref,
    _root_.Parser.Provenance.Table.mapRef]

theorem Origins.conversion_ancestry (origins : Origins model) :
    TracesTo origins.table origins.conversion (model.dae.flat.context.site .declaration) := by
  apply TracesTo.parent (parent := origins.literal) _ origins.initial_ancestry
  rw [origins.conversion_correct]
  simp [Node.parents]

theorem Origins.target_ancestry (origins : Origins model) :
    TracesTo origins.table origins.target (model.dae.flat.context.site .stateName) := by
  apply TracesTo.parent (parent := origins.fromSolve (model.sourceOrigin .stateName))
    _ (origins.fromSolve_trace _ _ (.source (model.source_origin .stateName)))
  rw [origins.target_correct]
  simp [Node.parents, fromSolve, _root_.Parser.Provenance.Table.Extension.ref,
    _root_.Parser.Provenance.Table.mapRef]

theorem Origins.write_ancestry (origins : Origins model) :
    TracesTo origins.table origins.write (model.dae.flat.context.site .declaration) := by
  apply TracesTo.parent (parent := origins.fromSolve model.origins.completion)
    _ (origins.fromSolve_trace _ _ model.completion_ancestry)
  rw [origins.write_correct]
  simp [Node.parents, fromSolve, _root_.Parser.Provenance.Table.Extension.ref,
    _root_.Parser.Provenance.Table.mapRef]

variable [interface : CInterface]

/-- The same origin-carrying emission executes the selected initialization and
retains the unchanged complete-behavior guarantee under supplied storage. -/
theorem Emission.preserves (emission : Emission model target)
    (env : CBody.Locals) (heap : Heap) (address : Address) (old : Option Value)
    (double : interface.types "double" = some .float64)
    (located : CBody.lvalue env heap target = some address)
    (storage : heap address = some ⟨.float64, true, old⟩) :
    emission.TraceCorrect ∧
    TracesTo emission.origins.table emission.origins.write (model.dae.flat.context.site .declaration) ∧
    (∀ behavior, CBody.machine.Behaves
      (.running [emission.statement, .ret none] env heap) behavior ↔
      behavior = .terminates ⟨.void, written heap address⟩) :=
  ⟨emission.trace_correct, emission.origins.write_ancestry,
    fun behavior => write_behaviors model target env heap address old double located storage behavior⟩

end Rumoca.CInitialization
