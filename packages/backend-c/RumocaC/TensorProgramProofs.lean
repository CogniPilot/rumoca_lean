import RumocaC.TensorProgramMemory
import RumocaC.TensorCalls
import RumocaC.TensorFillProofs

/-! Complete prepared Solve programs execute through the actual C helper calls.
Arithmetic domains include unused instructions. All behaviors terminate with
an exact finite source result and the complete planned memory frame. -/
noncomputable section
namespace Rumoca.CTensor.Lowering
open CTree CMemory CMemory.TensorView Solve.Tensor
variable [interface : CInterface]

structure Setup (locals : CBody.Locals) (definitions : CLoops.Calls.Definitions) : Prop where
  binaryHeader : CTensor.HeaderTypes interface
  fillHeader : Fill.HeaderTypes interface
  binaryDefined : ∀ op, definitions (CTensor.function op).signature.name = some (CTensor.function op)
  fillDefined : definitions Fill.function.signature.name = some Fill.function
  binaryUnshadowed : ∀ op, locals (CTensor.function op).signature.name = none
  fillUnshadowed : locals Fill.function.signature.name = none

theorem emit_correct (locals : CBody.Locals) (types : CLoops.Types) (locations : Locations)
    (definitions : CLoops.Calls.Definitions) (setup : Setup locals definitions)
    (p : Program Γ shape) (plan : Plan p) (layout : Layout Γ) (values : Env Binary64.Value Γ)
    (heap : Heap) (bound : LayoutBound locals locations layout)
    (represented : Represents locations layout heap values)
    (ready : Ready locals locations p plan layout heap) (domain : Finite.InDomain p values)
    (rest : List Stmt) (stack : CLoops.Calls.Continuation) :
    ∃ finalHeap, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.body (.running ((emit p plan layout).code ++ rest) locals types heap) stack)
      (.body (.running rest locals types finalHeap) stack) ∧
      Reads finalHeap (locations (emit p plan layout).result)
        (p.eval Finite.ops Binary64.positiveZero Binary64.one values) ∧
      Bound locals locations (emit p plan layout).result ∧
      (∀ q, Outside locations p plan q → finalHeap q = heap q) ∧
      (Writable heap (locations (emit p plan layout).result) shape.volume →
        Writable finalHeap (locations (emit p plan layout).result) shape.volume) := by
  induction p generalizing heap with
  | ret ref => exact ⟨heap, .refl _, represented ref, bound ref, fun _ _ => rfl, id⟩
  | fill s literal next ih =>
    rcases plan with ⟨destination, plan⟩
    rcases ready with ⟨writable, bounded, destBound, fresh, following⟩
    let result := Tensor.Value.fill s (literal.eval Binary64.positiveZero Binary64.one)
    let writtenHeap := written heap (locations destination) result s.volume
    have tailReady := ready_written locals locations next plan (layout.push destination) heap following .here result
    have tailReads : Represents locations (layout.push destination) writtenHeap (Env.push result values) :=
      represents_written locations layout destination heap values result represented fresh
    obtain ⟨finalHeap, ran, readResult, boundResult, frame, writableResult⟩ :=
      ih plan (layout.push destination) (Env.push result values) writtenHeap
        (bound_push locals locations layout destination bound destBound) tailReads tailReady domain
    have head := Fill.invoke_reaches definitions s (literal.eval Binary64.positiveZero Binary64.one)
      (locations destination) heap (CAlgorithm.literal literal) destination.pointer destination.count
      locals types ((emit next plan (layout.push destination)).code ++ rest) stack
      setup.fillDefined setup.fillHeader setup.fillUnshadowed
      (Fill.literal_eval literal locals heap setup.fillHeader.scalar)
      (destBound heap).1 (destBound heap).2 writable bounded
    refine ⟨finalHeap, head.trans ran, readResult, boundResult, ?_, ?_⟩
    · intro q outside
      exact (frame q outside.2).trans (written_frame heap (locations destination) result s.volume q outside.1)
    · exact fun hw => writableResult (written_preserves_writable heap (locations destination) result s.volume
        _ _ hw)

  | @binary _ s _ op left right next ih =>
    rcases plan with ⟨destination, plan⟩
    rcases ready with ⟨writable, bounded, destBound, fresh, following⟩
    rcases domain with ⟨arithmetic, domain⟩
    let result := op.eval Finite.ops (values left) (values right)
    let writtenHeap := written heap (locations destination) result s.volume
    have tailReady := ready_written locals locations next plan (layout.push destination) heap following .here result
    have tailReads : Represents locations (layout.push destination) writtenHeap (Env.push result values) :=
      represents_written locations layout destination heap values result represented fresh
    obtain ⟨finalHeap, ran, readResult, boundResult, frame, writableResult⟩ :=
      ih plan (layout.push destination) (Env.push result values) writtenHeap
        (bound_push locals locations layout destination bound destBound) tailReads tailReady domain
    have head := CTensor.invoke_reaches definitions op (values left) (values right) heap
      (locations (layout left)) (locations (layout right)) (locations destination)
      (layout left).pointer (layout right).pointer destination.pointer destination.count locals types
      ((emit next plan (layout.push destination)).code ++ rest) stack
      (setup.binaryDefined op) setup.binaryHeader (setup.binaryUnshadowed op)
      (bound left heap).1 (bound right heap).1 (destBound heap).1 (destBound heap).2
      (represented left) (represented right) writable (fresh left) (fresh right) arithmetic bounded
    refine ⟨finalHeap, head.trans ran, readResult, boundResult, ?_, ?_⟩
    · intro q outside
      exact (frame q outside.2).trans (written_frame heap (locations destination) result s.volume q outside.1)
    · exact fun hw => writableResult (written_preserves_writable heap (locations destination) result s.volume
        _ _ hw)

/-- Whole-fragment semantic preservation against independent finite Solve
execution. Every C behavior terminates, returns the source result buffer and
preserves all cells outside the explicitly planned destinations. -/
theorem emit_refines (locals : CBody.Locals) (types : CLoops.Types) (locations : Locations)
    (definitions : CLoops.Calls.Definitions) (setup : Setup locals definitions)
    (p : Program Γ shape) (plan : Plan p) (layout : Layout Γ) (values : Env Binary64.Value Γ)
    (result : Values shape) (heap : Heap) (bound : LayoutBound locals locations layout)
    (represented : Represents locations layout heap values)
    (ready : Ready locals locations p plan layout heap) (executed : Finite.Executes p values result) :
    ∃ finalHeap, Reads finalHeap (locations (emit p plan layout).result) result ∧
      Bound locals locations (emit p plan layout).result ∧
      (∀ q, Outside locations p plan q → finalHeap q = heap q) ∧
      (Writable heap (locations (emit p plan layout).result) shape.volume →
        Writable finalHeap (locations (emit p plan layout).result) shape.volume) ∧
      ∀ behavior, (CLoops.Calls.machine definitions).Behaves
        (.body (.running ((emit p plan layout).code ++ [.ret none]) locals types heap) .done) behavior ↔
        behavior = .terminates finalHeap := by
  obtain ⟨domain, resultEq⟩ := Finite.executes_sound executed
  obtain ⟨finalHeap, ran, readResult, boundResult, frame, writableResult⟩ :=
    emit_correct locals types locations definitions setup p plan layout values heap bound represented ready domain
      [.ret none] .done
  have returned : Transition.Reaches (CLoops.Calls.machine definitions).step
      (.body (.running [.ret none] locals types finalHeap) .done) (.halted finalHeap) :=
    .next (t := .body (.returned ⟨.void, finalHeap⟩) .done) (by rfl)
      (.next (t := .returning finalHeap .done) (by simp [CLoops.Calls.machine, CLoops.Calls.next])
        (.next (by rfl) (.refl _)))
  exact ⟨finalHeap, resultEq ▸ readResult, boundResult, frame, writableResult,
    fun _ => (CLoops.Calls.machine definitions).behavior_iff (ran.trans returned) rfl⟩

end Rumoca.CTensor.Lowering
