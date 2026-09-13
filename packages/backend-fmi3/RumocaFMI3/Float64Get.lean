import RumocaFMI3.Float64Read

noncomputable section
namespace Rumoca.FMI3.Float64Calls
open CTree CMemory CBody CLoops
variable [static : StaticLiterals]
private local instance getInterface : CInterface := cInterface static.addresses

/-- Complete successful public entry, both counted loops and converted return.
All iteration premises come from the original request/storage and the same
prepared numerical function table. The getter performs no solver advance. -/
theorem get_reaches (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (p input buffer : Address) (n : UInt64) (shape : Tensor.Shape)
    (references : Nat → UInt32) (kind : Kind) (mode : Mode) (state : ModelExchange.State)
    (time : Binary64.Value) (stack : CCalls.Typed.Continuation)
    (volume : shape.volume = n.toNat)
    (defined : program.internal.definitions (signature false).name =
      some (.tree (Runtime.function model (signature false))))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode)
    (readable : References heap (some input) shape.volume references)
    (valid : ∀ i < shape.volume, (references i).toNat ≤ 2)
    (writable : TensorView.Writable heap buffer shape.volume)
    (referencesSeparate : ∀ i < shape.volume, ∀ j < shape.volume, input.index i ≠ buffer.index j)
    (stateStored : StateProofs.Represents heap p state)
    (stateSeparate : ∀ i < shape.volume, StateProofs.stateAddress p ≠ buffer.index i)
    (timeStored : load heap (p.member "time") = some (.finite time))
    (timeSeparate : ∀ i < shape.volume, p.member "time" ≠ buffer.index i)
    (helper : program.internal.definitions "model_rhs" = some (.tree Runtime.helpers[1]))
    (numerical : program.internal.definitions "rumoca_rhs" = some (.kernel .rhs))
    (same : program.internal.kernel = CExecution.program model.solve) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.calling (signature false).name (arguments (some p) (some input) (some buffer) n n) heap stack)
      (.returning (.integer 0) (TensorView.written heap buffer
        (outputValues model state time shape (fun i => selectReference (references i))) shape.volume) stack) := by
  have bounded : shape.volume < 2 ^ 64 := volume ▸ n.toNat_lt_size
  have guarded := get_guard_run model heap p (some input) (some buffer) n n kind mode hk hm allowed
  rw [if_pos (by simp [ArrayAccess.Valid])] at guarded
  obtain ⟨types, entered⟩ := CCalls.Events.body_prefix_reaches program (Runtime.function model (signature false))
    (arguments (some p) (some input) (some buffer) n n) (parameters (some p) (some input) (some buffer) n n)
    (locals p (some input) (some buffer) n n) heap heap afterGuard stack 4
    defined (parameters_bound false _ _ _ _ _) (BodyEmbedding.body_closed model (signature false)) guarded
  let env := locals p (some input) (some buffer) n n
  let typed := bindType types "k" .size
  have ktype : typed "k" = some .size := by simp [typed, bindType]
  have count : resolve env "nValueReferences" = some (.integer shape.volume) := by
    simp [env, locals, parameters, CBody.bind, resolve, volume]
  have refBound : resolve env "valueReferences" = some (.pointer (some input)) := by
    simp [env, locals, parameters, CBody.bind, resolve]
  have initialized := counter_initialize env types heap "k"
    (loop "k" (Runtime.v "nValueReferences") [validation] :: afterValidation)
    (by simp [env, locals, parameters, CBody.bind]) (by rfl)
  refine entered.trans (.next (CCalls.Events.body_step program initialized "fmi3Status" stack) ?_)
  refine (validation_reaches program env typed heap (some input) shape.volume references
    afterValidation "fmi3Status" stack bounded ktype count refBound readable valid).trans ?_
  refine .next (CCalls.Events.body_step program (counter_reset env typed heap "k" shape.volume
    (loop "k" (Runtime.v "nValueReferences") readBody :: [Runtime.ok]) ktype) "fmi3Status" stack) ?_
  refine (read_reaches model program env typed heap p buffer (some input) shape references state time
    [Runtime.ok] "fmi3Status" stack bounded ktype count refBound
    (by simp [env, locals, parameters, CBody.bind, resolve])
    (by simp [env, locals, parameters, CBody.bind, resolve])
    (by simp [env, locals, parameters, CBody.bind]) readable valid writable
    (by intro base equal; cases Option.some.inj equal; exact referencesSeparate)
    stateStored stateSeparate timeStored timeSeparate helper numerical same).trans ?_
  exact DerivativeCalls.finish program _ (counterEnv env "k" shape.volume) typed stack
    (by simp [counterEnv, env, locals, parameters, CBody.bind])

theorem get_behaviors (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (p input buffer : Address) (n : UInt64) (shape : Tensor.Shape)
    (references : Nat → UInt32) (kind : Kind) (mode : Mode) (state : ModelExchange.State) (time : Binary64.Value)
    (volume : shape.volume = n.toNat)
    (defined : program.internal.definitions (signature false).name =
      some (.tree (Runtime.function model (signature false))))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode)
    (readable : References heap (some input) shape.volume references)
    (valid : ∀ i < shape.volume, (references i).toNat ≤ 2)
    (writable : TensorView.Writable heap buffer shape.volume)
    (referencesSeparate : ∀ i < shape.volume, ∀ j < shape.volume, input.index i ≠ buffer.index j)
    (stateStored : StateProofs.Represents heap p state)
    (stateSeparate : ∀ i < shape.volume, StateProofs.stateAddress p ≠ buffer.index i)
    (timeStored : load heap (p.member "time") = some (.finite time))
    (timeSeparate : ∀ i < shape.volume, p.member "time" ≠ buffer.index i)
    (helper : program.internal.definitions "model_rhs" = some (.tree Runtime.helpers[1]))
    (numerical : program.internal.definitions "rumoca_rhs" = some (.kernel .rhs))
    (same : program.internal.kernel = CExecution.program model.solve) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling (signature false).name (arguments (some p) (some input) (some buffer) n n) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, TensorView.written heap buffer
        (outputValues model state time shape (fun i => selectReference (references i))) shape.volume⟩ :=
  (CCalls.Events.internal_prefix program (get_reaches model program heap p input buffer n shape references
    kind mode state time .done volume defined hk hm allowed readable valid writable referencesSeparate
    stateStored stateSeparate timeStored timeSeparate helper numerical same)
    (CCalls.Events.return_forced program _ _)).behaviors behavior

end Rumoca.FMI3.Float64Calls

noncomputable section
namespace Rumoca.FMI3.Float64Calls
open CTree CMemory CBody CLoops
variable [static : StaticLiterals]
private local instance emptyInterface : CInterface := cInterface static.addresses

/-- A zero-length query may use null buffers. It reads no variable or numerical
kernel and leaves the entire heap unchanged. The instance still obeys its guard. -/
theorem empty_get_reaches (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (p : Address) (references values : Option Address) (kind : Kind) (mode : Mode)
    (stack : CCalls.Typed.Continuation)
    (defined : program.internal.definitions (signature false).name =
      some (.tree (Runtime.function model (signature false))))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.calling (signature false).name (arguments (some p) references values 0 0) heap stack)
      (.returning (.integer 0) heap stack) := by
  have guarded := get_guard_run model heap p references values 0 0 kind mode hk hm allowed
  rw [if_pos (by simp [ArrayAccess.Valid])] at guarded
  obtain ⟨types, entered⟩ := CCalls.Events.body_prefix_reaches program (Runtime.function model (signature false))
    (arguments (some p) references values 0 0) (parameters (some p) references values 0 0)
    (locals p references values 0 0) heap heap afterGuard stack 4
    defined (parameters_bound false _ _ _ _ _) (BodyEmbedding.body_closed model (signature false)) guarded
  let env := locals p references values 0 0
  let typed := bindType types "k" .size
  have ktype : typed "k" = some .size := by simp [typed, bindType]
  have counter : counterEnv env "k" 0 "k" = some (.integer 0) := by simp [counterEnv, CBody.bind]
  have count : CBody.eval (counterEnv env "k" 0) heap (Runtime.v "nValueReferences") = some (.integer 0) := by
    simp [Runtime.v, CBody.eval, counterEnv, env, locals, parameters, CBody.bind, resolve]
  have initialized := counter_initialize env types heap "k"
    (loop "k" (Runtime.v "nValueReferences") [validation] :: afterValidation)
    (by simp [env, locals, parameters, CBody.bind]) (by rfl)
  refine entered.trans (.next (CCalls.Events.body_step program initialized "fmi3Status" stack) ?_)
  refine .next (CCalls.Events.body_step program (CLoops.loop_stop _ _ _ "k"
    (Runtime.v "nValueReferences") [validation] afterValidation 0 counter count
    (by simpa using validation_closed)) "fmi3Status" stack) ?_
  refine .next (CCalls.Events.body_step program (counter_reset env typed heap "k" 0
    (loop "k" (Runtime.v "nValueReferences") readBody :: [Runtime.ok]) ktype) "fmi3Status" stack) ?_
  refine .next (CCalls.Events.body_step program (CLoops.loop_stop _ _ _ "k"
    (Runtime.v "nValueReferences") readBody [Runtime.ok] 0 counter count read_closed) "fmi3Status" stack) ?_
  exact DerivativeCalls.finish program heap (counterEnv env "k" 0) typed stack
    (by simp [counterEnv, env, locals, parameters, CBody.bind])

theorem empty_get_behaviors (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (p : Address) (references values : Option Address) (kind : Kind) (mode : Mode)
    (defined : program.internal.definitions (signature false).name =
      some (.tree (Runtime.function model (signature false))))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling (signature false).name (arguments (some p) references values 0 0) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, heap⟩ :=
  (CCalls.Events.internal_prefix program (empty_get_reaches model program heap p references values kind mode .done
    defined hk hm allowed) (CCalls.Events.return_forced program _ _)).behaviors behavior

theorem null_get_behaviors (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (references values : Option Address) (n m : UInt64)
    (defined : program.internal.definitions (signature false).name =
      some (.tree (Runtime.function model (signature false)))) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling (signature false).name (arguments none references values n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  apply GuardedCalls.null_behaviors program (Runtime.function model (signature false))
    (Runtime.modeGuard .get :: getTail) (arguments none references values n m) (parameters none references values n m)
    heap defined (parameters_bound false _ _ _ _ _) rfl rfl (BodyEmbedding.body_closed model (signature false))
  all_goals simp [parameters, CBody.bind]

end Rumoca.FMI3.Float64Calls
