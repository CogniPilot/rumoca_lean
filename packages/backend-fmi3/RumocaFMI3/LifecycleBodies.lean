import RumocaFMI3.HistoryBodies

/-! Mode writes and successful termination in the shared C execution model.
The error-helper theorem reaches its logger after entering Terminated; callback
execution, the final error return and actual adapter bytes remain separate. -/
namespace Rumoca.FMI3.LifecycleBodies
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses
open CTree CMemory CBody

def writeMode (heap : Heap) (p : Address) (mode : Mode) : Heap :=
  replace heap (p.member "mode") ⟨.int32, true, some (.integer mode.code)⟩

omit static in
theorem write_frame (heap : Heap) (p q : Address) (mode : Mode)
    (hq : q ≠ p.member "mode") : writeMode heap p mode q = heap q :=
  replace_other _ _ _ _ hq

omit static in
theorem write_mode (heap : Heap) (p : Address) (mode : Mode) :
    load (writeMode heap p mode) (p.member "mode") = some (.integer mode.code) := by
  cases mode <;> simp [writeMode, load, convert, Mode.code]

theorem write_run (env : Locals) (heap : Heap) (p : Address) (mode : Mode)
    (old : Option Value) (rest : List Stmt)
    (hp : resolve env "m" = some (.pointer (some p)))
    (hm : heap (p.member "mode") = some ⟨.int32, true, old⟩) :
    run 1 (.running (Runtime.setMode mode :: rest) env heap) =
      some (.running rest env (writeMode heap p mode)) := by
  cases mode <;> simp [run, next, Runtime.setMode, Runtime.put, Runtime.field,
    Runtime.v, Runtime.mode, Runtime.n, Mode.code, eval, lvalue, hp, Value.address,
    store, hm, convert, writeMode]

omit static in
theorem write_history (h : HistoryProofs.Stored heap p c) (mode : Mode) :
    HistoryProofs.Stored (writeMode heap p mode) p c := by
  rcases h with ⟨ht, hn, he, hl⟩
  constructor <;> simp_all [writeMode, replace]

omit static in
theorem write_model (h : StateProofs.Represents heap p state) (mode : Mode) :
    StateProofs.Represents (writeMode heap p mode) p state := by
  have hf := write_frame heap p (StateProofs.stateAddress p) mode
    (HistoryBodies.state_ne_field p "mode")
  simpa only [StateProofs.Represents, load, hf] using h

/-- The first statement of the actual error helper writes its failure mode;
logging and the final return are deliberately left in the continuation. -/
theorem failure_mode_run (env : Locals) (heap : Heap) (p : Address) (old : Option Value)
    (hp : resolve env "m" = some (.pointer (some p)))
    (hm : heap (p.member "mode") = some ⟨.int32, true, old⟩) :
    run 1 (.running Runtime.helpers[0].body env heap) =
      some (.running [Runtime.log "fmi3Error" (Runtime.v "message"), Runtime.ret (Runtime.v "fmi3Error")]
        env (writeMode heap p .terminated)) := by
  simpa [Runtime.helpers] using write_run env heap p .terminated old
    [Runtime.log "fmi3Error" (Runtime.v "message"), Runtime.ret (Runtime.v "fmi3Error")] hp hm

theorem terminate_run (m : Solve.FMI3Model source) (sig : Signature)
    (hsig : sig.name = "fmi3Terminate") (heap : Heap) (p : Address) (kind : Kind) (mode : Mode)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (ha : Reference.Allowed .terminate kind mode) :
    run 5 (.running (Runtime.body m sig) (HistoryBodies.parameters p) heap) =
      some (.returned ⟨.integer 0, writeMode heap p .terminated⟩) := by
  have hmode : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have hp := LifecycleGuard.accept (HistoryBodies.parameters p) heap p .terminate kind mode
    [Runtime.setMode .terminated, Runtime.ok]
    (by simp [HistoryBodies.parameters]) (by simp [HistoryBodies.parameters]) hk hmode ha
  rw [show Runtime.body m sig = Runtime.require .terminate ++
    [Runtime.setMode .terminated, Runtime.ok] by simp [Runtime.body, hsig]]
  rw [show 5 = 3 + 2 from rfl, run_add, hp]
  simp [run, next, Runtime.setMode, Runtime.put, Runtime.field, Runtime.v,
    Runtime.mode, Runtime.n, Runtime.ok, Runtime.ret, Mode.code, eval, lvalue,
    HistoryBodies.parameters, CBody.bind, resolve, constants, Value.address,
    store, hm, convert, writeMode]

noncomputable section
/-- Every successful termination body returns OK and changes only lifecycle
mode. The model and clock values remain available to final-value queries. -/
theorem terminate_correct (m : Solve.FMI3Model source) (sig : Signature)
    (hsig : sig.name = "fmi3Terminate") (heap : Heap) (p : Address) (kind : Kind) (mode : Mode)
    (c : Time.Clock) (state : ModelExchange.State)
    (hc : HistoryProofs.Stored heap p c) (hx : StateProofs.Represents heap p state)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (ha : Reference.Allowed .terminate kind mode) :
    (∀ b, (CCalls.machine (CallProofs.linked m)).Behaves
      (.body (.running (Runtime.body m sig) (HistoryBodies.parameters p) heap) "fmi3Status" .done) b ↔
      b = .terminates ⟨.integer 0, writeMode heap p .terminated⟩) ∧
    HistoryProofs.Stored (writeMode heap p .terminated) p c ∧
    StateProofs.Represents (writeMode heap p .terminated) p state ∧
    load (writeMode heap p .terminated) (p.member "mode") = some (.integer Mode.terminated.code) :=
  ⟨fun b => CCalls.body_behaviors _ (terminate_run m sig hsig heap p kind mode hk hm ha)
    (by simp [CCalls.returnCast, CBody.cast, convert]) b,
   write_history hc .terminated, write_model hx .terminated, write_mode heap p .terminated⟩
end
end Rumoca.FMI3.LifecycleBodies
