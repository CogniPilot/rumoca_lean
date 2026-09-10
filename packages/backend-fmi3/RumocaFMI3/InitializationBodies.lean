import RumocaFMI3.HistoryBodies

/-! Successful exit from initialization in the existing event-free FMI profile
(FMI 3.0.2 §2.3.3). The complete generated body changes lifecycle mode and
preserves the model, history and unrelated memory. Public ABI entry, rejected
calls and printed-adapter binding remain separate obligations. -/
namespace Rumoca.FMI3.InitializationBodies
private local instance targetInterface : CInterface := cInterface
open CTree CMemory CBody

def kindCode : Kind → Int
  | .me => 0
  | .cs => 1

def exitHeap (heap : Heap) (p : Address) (kind : Kind) : Heap :=
  replace heap (p.member "mode")
    ⟨.int32, true, some (.integer (nextMode .exitInitialization kind .initialization).code)⟩

theorem exit_frame (heap : Heap) (p q : Address) (kind : Kind)
    (hq : q ≠ p.member "mode") : exitHeap heap p kind q = heap q :=
  replace_other _ _ _ _ hq

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem exit_run (m : Solve.FMI3Model source) (sig : Signature)
    (hsig : sig.name = "fmi3ExitInitializationMode") (heap : Heap) (p : Address) (kind : Kind)
    (hk : load heap (p.member "kind") = some (.integer (kindCode kind)))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer 1)⟩) :
    run 6 (.running (Runtime.body m sig) (HistoryBodies.parameters p) heap) =
      some (.returned ⟨.integer 0, exitHeap heap p kind⟩) := by
  have hmode : load heap (p.member "mode") = some (.integer 1) := by
    simp [load, hm, convert]
  let tail := [Runtime.branch (Runtime.eqv (Runtime.field "kind") (Runtime.n 0))
    [Runtime.setMode .event] [Runtime.setMode .step], Runtime.ok]
  have hk' : load heap (p.member "kind") = some (.integer kind.code) := by
    cases kind <;> exact hk
  have hp := LifecycleGuard.accept (HistoryBodies.parameters p) heap p
    .exitInitialization kind .initialization tail
    (by simp [HistoryBodies.parameters]) (by simp [HistoryBodies.parameters]) hk' hmode rfl
  have hb : Runtime.body m sig = Runtime.require .exitInitialization ++ tail := by
    simp [Runtime.body, hsig, tail]
  rw [hb, show 6 = 3 + 3 from rfl, run_add, hp]
  cases kind <;>
    simp [tail, Runtime.mode, Mode.code,
      Runtime.branch, Runtime.ret, Runtime.ok, Runtime.put, Runtime.setMode,
      Runtime.field, Runtime.eqv, Runtime.v, Runtime.n,
      run, next, eval, lvalue, HistoryBodies.parameters, CBody.bind, resolve, constants,
      convert, comparison, boolean, Value.truth, Value.address,
      hk, hm, store, exitHeap, kindCode, me_initialization, cs_initialization]

theorem exit_mode (heap : Heap) (p : Address) (kind : Kind) :
    load (exitHeap heap p kind) (p.member "mode") =
      some (.integer (nextMode .exitInitialization kind .initialization).code) := by
  cases kind <;> simp [exitHeap, me_initialization, cs_initialization,
    load, replace, convert, Mode.code]

theorem exit_history (h : HistoryProofs.Stored heap p c) (kind : Kind) :
    HistoryProofs.Stored (exitHeap heap p kind) p c := by
  rcases h with ⟨ht, hn, he, hl⟩
  constructor <;> simp_all [exitHeap, replace]

theorem exit_model (h : StateProofs.Represents heap p state) (kind : Kind) :
    StateProofs.Represents (exitHeap heap p kind) p state := by
  have hf := exit_frame heap p (StateProofs.stateAddress p) kind
    (HistoryBodies.state_ne_field p "mode")
  simpa only [StateProofs.Represents, load, hf] using h

noncomputable section
theorem exit_behaviors (m : Solve.FMI3Model source) (sig : Signature)
    (hsig : sig.name = "fmi3ExitInitializationMode") (heap : Heap) (p : Address) (kind : Kind)
    (hk : load heap (p.member "kind") = some (.integer (kindCode kind)))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer 1)⟩) (b) :
    (CCalls.machine (CallProofs.linked m)).Behaves
      (.body (.running (Runtime.body m sig) (HistoryBodies.parameters p) heap) "fmi3Status" .done) b ↔
      b = .terminates ⟨.integer 0, exitHeap heap p kind⟩ :=
  CCalls.body_behaviors _ (exit_run m sig hsig heap p kind hk hm)
    (by simp [CCalls.returnCast, CBody.cast, convert]) b

/-- Every behavior of the complete successful body returns OK, enters the
reference lifecycle mode, and preserves the shared model and clock history. -/
theorem exit_correct (m : Solve.FMI3Model source) (sig : Signature)
    (hsig : sig.name = "fmi3ExitInitializationMode") (heap : Heap) (p : Address) (kind : Kind)
    (c : Time.Clock) (state : ModelExchange.State)
    (hc : HistoryProofs.Stored heap p c) (hx : StateProofs.Represents heap p state)
    (hk : load heap (p.member "kind") = some (.integer (kindCode kind)))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer 1)⟩) :
    (∀ b, (CCalls.machine (CallProofs.linked m)).Behaves
      (.body (.running (Runtime.body m sig) (HistoryBodies.parameters p) heap) "fmi3Status" .done) b ↔
      b = .terminates ⟨.integer 0, exitHeap heap p kind⟩) ∧
    HistoryProofs.Stored (exitHeap heap p kind) p c ∧
    StateProofs.Represents (exitHeap heap p kind) p state ∧
    load (exitHeap heap p kind) (p.member "mode") =
      some (.integer (nextMode .exitInitialization kind .initialization).code) :=
  ⟨exit_behaviors m sig hsig heap p kind hk hm, exit_history hc kind,
    exit_model hx kind, exit_mode heap p kind⟩

end
end Rumoca.FMI3.InitializationBodies
