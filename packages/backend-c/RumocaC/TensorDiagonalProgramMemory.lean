import RumocaC.TensorDiagonalProgramCode
import RumocaC.TensorProgramMemory

namespace Rumoca.CTensor.Lowering
open CTree CMemory CMemory.TensorView Solve.Tensor
/-- The output is separate from entry registers and every planned destination.
This reserves its writable cells across coefficient production. -/
def Reserved (locations : Locations) (output : Buffer targetShape)
    (p : Program Γ shape) (plan : Plan p) (layout : Layout Γ) : Prop :=
  Fresh locations output layout ∧ ∀ i < targetShape.volume, Outside locations p plan ((locations output).index i)

theorem fresh_push (locations : Locations) (output : Buffer targetShape) (layout : Layout Γ)
    (destination : Buffer shape) (fresh : Fresh locations output layout)
    (separate : ∀ i < targetShape.volume, ∀ j < shape.volume,
      (locations output).index i ≠ (locations destination).index j) :
    Fresh locations output (layout.push destination) := by
  intro s ref
  cases ref with
  | here => exact separate
  | there ref => exact fresh ref

theorem reserved_result (locations : Locations) (output : Buffer targetShape)
    (p : Program Γ shape) (plan : Plan p) (layout : Layout Γ)
    (reserved : Reserved locations output p plan layout) :
    ∀ i < targetShape.volume, ∀ j < shape.volume,
      (locations output).index i ≠ (locations (emit p plan layout).result).index j := by
  induction p with
  | ret ref => exact reserved.1 ref
  | fill s literal next ih =>
    exact ih plan.2 (layout.push plan.1)
      ⟨fresh_push locations output layout plan.1 reserved.1 (fun i hi => (reserved.2 i hi).1),
        fun i hi => (reserved.2 i hi).2⟩
  | @binary _ s _ op left right next ih =>
    exact ih plan.2 (layout.push plan.1)
      ⟨fresh_push locations output layout plan.1 reserved.1 (fun i hi => (reserved.2 i hi).1),
        fun i hi => (reserved.2 i hi).2⟩

theorem reserved_writable (locations : Locations) (output : Buffer targetShape)
    (p : Program Γ shape) (plan : Plan p) (layout : Layout Γ) (heap following : Heap)
    (reserved : Reserved locations output p plan layout)
    (writable : Writable heap (locations output) targetShape.volume)
    (frame : ∀ q, Outside locations p plan q → following q = heap q) :
    Writable following (locations output) targetShape.volume := by
  intro i hi
  obtain ⟨old, cell⟩ := writable i hi
  exact ⟨old, (frame _ (reserved.2 i hi)).trans cell⟩

def DiagonalOutside (locations : Locations) (p : DiagonalProgram Γ shape) (plan : Plan p.coefficients)
    (output : Buffer p.shape) (q : Address) : Prop :=
  Outside locations p.coefficients plan q ∧ ∀ i < p.shape.volume, q ≠ (locations output).index i

end Rumoca.CTensor.Lowering
