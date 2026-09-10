import RumocaC.TensorProgramCode
import RumocaC.TensorMemory
import RumocaC.Body

/-! Initial storage and stable argument bindings for complete tensor programs.
Future destinations are writable and fresh in the initial heap. The preservation
lemmas derive later readiness; no intermediate execution is a premise. -/
namespace Rumoca.CTensor.Lowering
open CTree CMemory CMemory.TensorView Solve.Tensor

noncomputable section
variable [interface : CInterface]

abbrev Locations := {shape : Tensor.Shape} → Buffer shape → Address

def Bound (locals : CBody.Locals) (locations : Locations) (buffer : Buffer shape) : Prop :=
  ∀ heap, CBody.eval locals heap buffer.pointer = some (.pointer (some (locations buffer))) ∧
    CBody.eval locals heap buffer.count = some (.integer shape.volume)

def LayoutBound (locals : CBody.Locals) (locations : Locations) (layout : Layout Γ) : Prop :=
  ∀ {s} (ref : Ref Γ s), Bound locals locations (layout ref)

def Represents (locations : Locations) (layout : Layout Γ) (heap : Heap) (values : Env Binary64.Value Γ) : Prop :=
  ∀ {s} (ref : Ref Γ s), Reads heap (locations (layout ref)) (values ref)

def Fresh (locations : Locations) (destination : Buffer shape) (layout : Layout Γ) : Prop :=
  ∀ {s} (ref : Ref Γ s), ∀ i < shape.volume, ∀ j < s.volume,
    (locations destination).index i ≠ (locations (layout ref)).index j

/-- Every future buffer is checked against the original heap. Freshness
includes all earlier registers, without assuming any intermediate result. -/
def Ready (locals : CBody.Locals) (locations : Locations) :
    (p : Program Γ shape) → Plan p → Layout Γ → Heap → Prop
  | .ret _ => fun _ _ _ => True
  | .fill s _ next => fun plan layout heap =>
      Writable heap (locations plan.1) s.volume ∧ s.volume < 2 ^ 64 ∧
      Bound locals locations plan.1 ∧ Fresh locations plan.1 layout ∧
      Ready locals locations next plan.2 (layout.push plan.1) heap
  | @Program.binary _ s _ _ _ _ next => fun plan layout heap =>
      Writable heap (locations plan.1) s.volume ∧ s.volume < 2 ^ 64 ∧
      Bound locals locations plan.1 ∧ Fresh locations plan.1 layout ∧
      Ready locals locations next plan.2 (layout.push plan.1) heap

def Outside (locations : Locations) : (p : Program Γ shape) → Plan p → Address → Prop
  | .ret _ => fun _ _ => True
  | .fill s _ next => fun plan q =>
      (∀ i < s.volume, q ≠ (locations plan.1).index i) ∧ Outside locations next plan.2 q
  | @Program.binary _ s _ _ _ _ next => fun plan q =>
      (∀ i < s.volume, q ≠ (locations plan.1).index i) ∧ Outside locations next plan.2 q

theorem bound_push (locals : CBody.Locals) (locations : Locations) (layout : Layout Γ)
    (destination : Buffer shape) (bound : LayoutBound locals locations layout)
    (destBound : Bound locals locations destination) :
    LayoutBound locals locations (layout.push destination) := by
  intro s ref
  cases ref with
  | here => exact destBound
  | there ref => exact bound ref

omit interface in
theorem represents_written (locations : Locations) (layout : Layout Γ)
    (destination : Buffer shape) (heap : Heap) (values : Env Binary64.Value Γ) (result : Values shape)
    (represented : Represents locations layout heap values) (fresh : Fresh locations destination layout) :
    Represents locations (layout.push destination)
      (written heap (locations destination) result shape.volume) (Env.push result values) := by
  intro s ref
  cases ref with
  | here => exact written_reads _ _ _
  | there ref =>
    intro i
    have frame := written_frame heap (locations destination) result shape.volume
      ((locations (layout ref)).index i.val) (fun j hj => Ne.symm (fresh ref j hj i.val i.isLt))
    simpa only [Layout.push, Env.push, load, frame] using represented ref i

omit interface in
theorem writable_written (heap : Heap) (output input : Address) (values : Values shape) (count : Nat)
    (writable : Writable heap output count)
    (separate : ∀ i < count, ∀ j < shape.volume, output.index i ≠ input.index j) :
    Writable (written heap input values shape.volume) output count := by
  intro i hi
  obtain ⟨old, stored⟩ := writable i hi
  exact ⟨old, (written_frame heap input values shape.volume (output.index i) (separate i hi)).trans stored⟩

/-- Writing an existing input register cannot invalidate any fresh future
destination. This supplies the induction step from the initial allocation. -/
theorem ready_written (locals : CBody.Locals) (locations : Locations)
    (p : Program Γ shape) (plan : Plan p) (layout : Layout Γ) (heap : Heap)
    (ready : Ready locals locations p plan layout heap)
    (ref : Ref Γ s) (values : Values s) :
    Ready locals locations p plan layout (written heap (locations (layout ref)) values s.volume) := by
  induction p with
  | ret => trivial
  | fill shape value next ih =>
    rcases plan with ⟨destination, plan⟩
    rcases ready with ⟨writable, bounded, bound, fresh, following⟩
    exact ⟨writable_written heap _ _ values _ writable (fresh ref), bounded, bound, fresh,
      ih plan (layout.push destination) following (.there ref)⟩
  | @binary _ s _ op left right next ih =>
    rcases plan with ⟨destination, plan⟩
    rcases ready with ⟨writable, bounded, bound, fresh, following⟩
    exact ⟨writable_written heap _ _ values _ writable (fresh ref), bounded, bound, fresh,
      ih plan (layout.push destination) following (.there ref)⟩

end
end Rumoca.CTensor.Lowering
