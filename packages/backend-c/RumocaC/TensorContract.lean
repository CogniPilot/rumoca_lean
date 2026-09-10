import RumocaC.TensorSyntax
import RumocaC.TensorProofs

/-! Text-to-execution contract for the development tensor helpers. This binds
the independent lexical/token grammar to all behaviors of the authored C
body and the independent finite Solve relation, including the output and
whole-heap frame. It is a helper-body theorem, not a function-call ABI,
whole-program allocation or source-to-FMU theorem. -/
noncomputable section
namespace Rumoca.CTensor
open CMemory CMemory.TensorView Solve.Tensor

def BodyBehaves [CInterface] (source : String) (env : CBody.Locals) (types : CLoops.Types)
    (heap : Heap) (behavior : Transition.Observation CBody.Result) : Prop :=
  ∃ op, Syntax.Denotes source op ∧
    CLoops.machine.Behaves (.running (function op).body env types heap) behavior

def Outcome (op : Tensor.BinaryOp) (a b : Values shape) (heap : Heap) (output : Address)
    (behavior : Transition.Observation CBody.Result) : Prop :=
  ∃ result : Values shape, Finite.Pointwise op a b result ∧
    behavior = .terminates ⟨.void, written heap output result shape.volume⟩ ∧
    Reads (written heap output result shape.volume) output result ∧
    ∀ q, (∀ i < shape.volume, q ≠ output.index i) →
      written heap output result shape.volume q = heap q

theorem body_correct [interface : CInterface] (source : String) (op : Tensor.BinaryOp)
    (denoted : Syntax.Denotes source op) (a b : Values shape)
    (heap : Heap) (left right output : Address)
    (read_left : Reads heap left a) (read_right : Reads heap right b)
    (write_output : Writable heap output shape.volume)
    (separate_left : Separate output left shape.volume) (separate_right : Separate output right shape.volume)
    (domain : ∀ i : Fin shape.volume, Finite.Domain op a[i] b[i]) (bounded : shape.volume < 2 ^ 64)
    (size_type : interface.types "size_t" = some .size) (behavior) :
    BodyBehaves source (parameters left right output shape.volume) parameterTypes heap behavior ↔
      Outcome op a b heap output behavior := by
  have hc := function_correct op a b heap left right output read_left read_right write_output
    separate_left separate_right domain bounded size_type behavior
  constructor
  · rintro ⟨parsed, parsed_source, ran⟩
    have he : parsed = op := Syntax.denotes_unique parsed_source denoted
    subst parsed
    exact ⟨op.eval Finite.ops a b, (Finite.pointwise_iff _ _ _ _).mpr ⟨domain, rfl⟩,
      hc.mp ran, written_reads _ _ _, written_frame _ _ _ _⟩
  · rintro ⟨result, finite, ran, _, _⟩
    have he := ((Finite.pointwise_iff _ _ _ _).mp finite).2
    subst result
    exact ⟨op, denoted, hc.mpr ran⟩

def ArtifactContract (source : String) (op : Tensor.BinaryOp) : Prop :=
  Syntax.Denotes source op ∧
  ∀ (interface : CInterface) (shape : Tensor.Shape) (a b : Values shape)
    (heap : Heap) (left right output : Address),
    Reads heap left a → Reads heap right b → Writable heap output shape.volume →
    Separate output left shape.volume → Separate output right shape.volume →
    (∀ i : Fin shape.volume, Finite.Domain op a[i] b[i]) → shape.volume < 2 ^ 64 →
    interface.types "size_t" = some .size → ∀ behavior,
    @BodyBehaves interface source (parameters left right output shape.volume) parameterTypes heap behavior ↔
      Outcome op a b heap output behavior

/-- Printing the helper supplies its full finite operator/body contract.
The equality premise is separately checked against the actual emitted file. -/
theorem artifact_correct (op : Tensor.BinaryOp) (source : String)
    (emitted : source = (function op).render) : ArtifactContract source op := by
  have denoted : Syntax.Denotes source op := emitted ▸ Syntax.render_denotes op
  refine ⟨denoted, ?_⟩
  intro interface shape a b heap left right output hl hr hw sl sr domain bounded size_type behavior
  exact @body_correct shape interface source op denoted a b heap left right output
    hl hr hw sl sr domain bounded size_type behavior

end Rumoca.CTensor
