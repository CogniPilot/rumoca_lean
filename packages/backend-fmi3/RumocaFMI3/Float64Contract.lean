import RumocaFMI3.Float64Failures
import RumocaFMI3.LoggingContract
import RumocaC.ObservedCalls
import RumocaFMI3.ModelRhs
import RumocaFMI3.Float64Metadata

noncomputable section
namespace Rumoca.FMI3.Float64Calls
open CTree CMemory CLiteral CCalls.Events

def FailureExecutionContract [interface : CInterface] (reason : GetFailure)
    (program : CCalls.Events.Program Invocation) (category message : Address) (heap : Heap) (signed : Bool) : Prop :=
  ∀ (p logger : Address) (environment input buffer : Option Address) (n m : UInt64)
    (references : Nat → UInt32) (kind : Kind) (mode : Mode)
    (name : String) (effect : ReturningEffect (Logging.signature name)),
    program.addresses logger = some name →
    program.externals name = some (External.observed (Logging.signature name) effect) →
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    Reference.Allowed .get kind mode →
    (reason = .reference → References heap input n.toNat references) →
    FailureCondition reason input buffer n m references →
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (signature false).name (arguments (some p) input buffer n m) heap .done) behavior ↔
      (∃ value after, effect.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) value after ∧
        behavior = .terminates [⟨name, Logging.arguments environment category message⟩] ⟨.integer 3, after⟩) ∨
      ((∀ value after, ¬ effect.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) value after) ∧ behavior = .wrong [])) ∧
    (∀ value after, effect.execute (Logging.arguments environment category message)
      (LifecycleBodies.writeMode heap p .terminated) value after →
      Stored signed after category "logStatus" ∧ Stored signed after message (failureMessage reason))

def SilentExecutionContract [interface : CInterface] (reason : GetFailure)
    (program : CCalls.Events.Program E) (heap : Heap) : Prop :=
  ∀ p input buffer n m references kind mode logger,
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (.integer 0) →
    Reference.Allowed .get kind mode →
    (reason = .reference → References heap input n.toNat references) →
    FailureCondition reason input buffer n m references →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (signature false).name (arguments (some p) input buffer n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩

section
variable [static : StaticLiterals]
private local instance errorInterface : CInterface := cInterface static.addresses

theorem failure_execution_correct (model : Solve.FMI3Model source) (reason : GetFailure)
    (program : CCalls.Events.Program Invocation) (category message : Address) (heap : Heap) (signed : Bool)
    (defined : program.internal.definitions (signature false).name =
      some (.tree (Runtime.function model (signature false))))
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (literal : static.addresses "logStatus" = some category)
    (messageBound : static.addresses (failureMessage reason) = some message)
    (categoryStored : Stored signed heap category "logStatus")
    (messageStored : Stored signed heap message (failureMessage reason)) :
    FailureExecutionContract reason program category message heap signed := by
  intro p logger environment input buffer n m references kind mode name effect
    address external hk hm hl hg he allowed readable condition
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have certified := failure_site model program heap p input buffer n m references kind mode reason
    defined hk modeLoaded allowed readable condition
  have all := GuardedCalls.FailureSite.all_behaviors program _ heap p message category logger
    (failureMessage reason) name environment _ (External.observed (Logging.signature name) effect)
    certified helper messageBound address external rfl literal hm hl hg he
  constructor
  · intro behavior
    exact (all behavior).trans (observed_choices effect _ _ (fun _ after => ⟨.integer 3, after⟩) behavior)
  · intro value after executed
    have successful := (all (.terminates [⟨name, Logging.arguments environment category message⟩]
      ⟨.integer 3, after⟩)).mpr (Or.inl ⟨_, value, after, ⟨rfl, executed⟩, rfl⟩)
    have preserved := CCalls.Events.termination_preserves successful
    exact ⟨categoryStored.preserved preserved, messageStored.preserved preserved⟩

theorem silent_execution_correct (model : Solve.FMI3Model source) (reason : GetFailure)
    (program : CCalls.Events.Program E) (message : Address) (heap : Heap)
    (defined : program.internal.definitions (signature false).name =
      some (.tree (Runtime.function model (signature false))))
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (messageBound : static.addresses (failureMessage reason) = some message) :
    SilentExecutionContract reason program heap := by
  intro p input buffer n m references kind mode logger hk hm hl hg allowed readable condition behavior
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have certified := failure_site model program heap p input buffer n m references kind mode reason
    defined hk modeLoaded allowed readable condition
  exact GuardedCalls.FailureSite.silent_behaviors program _ heap p message (failureMessage reason)
    _ logger certified helper messageBound hm hl hg behavior

end
end Rumoca.FMI3.Float64Calls

noncomputable section
namespace Rumoca.FMI3.Float64Calls
open CTree CMemory CLiteral CCalls.Events

structure QuietExecutionContract [interface : CInterface] (model : Solve.FMI3Model source)
    (program : CCalls.Events.Program E) (heap : Heap) : Prop where
  get : ∀ (p input buffer : Address) (n : UInt64) (shape : Tensor.Shape)
    (references : Nat → UInt32) (kind : Kind) (mode : Mode) (state : ModelExchange.State) (time : Binary64.Value),
    shape.volume = n.toNat →
    load heap (p.member "kind") = some (.integer kind.code) →
    load heap (p.member "mode") = some (.integer mode.code) →
    Reference.Allowed .get kind mode →
    References heap (some input) shape.volume references →
    (∀ i < shape.volume, (references i).toNat ≤ 2) →
    TensorView.Writable heap buffer shape.volume →
    (∀ i < shape.volume, ∀ j < shape.volume, input.index i ≠ buffer.index j) →
    StateProofs.Represents heap p state →
    (∀ i < shape.volume, StateProofs.stateAddress p ≠ buffer.index i) →
    load heap (p.member "time") = some (.finite time) →
    (∀ i < shape.volume, p.member "time" ≠ buffer.index i) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (signature false).name (arguments (some p) (some input) (some buffer) n n) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, TensorView.written heap buffer
        (outputValues model state time shape (fun i => selectReference (references i))) shape.volume⟩
  empty : ∀ p input buffer kind mode,
    load heap (p.member "kind") = some (.integer kind.code) →
    load heap (p.member "mode") = some (.integer mode.code) →
    Reference.Allowed .get kind mode →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (signature false).name (arguments (some p) input buffer 0 0) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, heap⟩
  null : ∀ input buffer n m behavior, (CCalls.Events.machine program).Behaves
    (.calling (signature false).name (arguments none input buffer n m) heap .done) behavior ↔
    behavior = .terminates [] ⟨.integer 3, heap⟩

section
variable [static : StaticLiterals]
private local instance quietInterface : CInterface := cInterface static.addresses

theorem quiet_execution_correct (model : Solve.FMI3Model source)
    (program : CCalls.Events.Program E) (heap : Heap)
    (defined : program.internal.definitions (signature false).name =
      some (.tree (Runtime.function model (signature false))))
    (helper : program.internal.definitions "model_rhs" = some (.tree Runtime.helpers[1]))
    (numerical : program.internal.definitions "rumoca_rhs" = some (.kernel .rhs))
    (same : program.internal.kernel = CExecution.program model.solve) : QuietExecutionContract model program heap := by
  constructor
  · intro p input buffer n shape references kind mode state time volume hk hm allowed readable valid
      writable referencesSeparate stateStored stateSeparate timeStored timeSeparate behavior
    exact get_behaviors model program heap p input buffer n shape references kind mode state time volume
      defined hk hm allowed readable valid writable referencesSeparate stateStored stateSeparate
      timeStored timeSeparate helper numerical same behavior
  · intro p input buffer kind mode hk hm allowed behavior
    exact empty_get_behaviors model program heap p input buffer kind mode defined hk hm allowed behavior
  · intro input buffer n m behavior
    exact null_get_behaviors model program heap input buffer n m defined behavior

end

def PreparedContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)) : Prop :=
  ∀ (before : Heap) (firstBlock : Nat) (signed : Bool), ∃ (category : Address) (messages : GetFailure → Address),
    pool.addresses firstBlock "logStatus" = some category ∧
    Stored signed (pool.install before firstBlock signed) category "logStatus" ∧
    (∀ reason, pool.addresses firstBlock (failureMessage reason) = some (messages reason) ∧
      Stored signed (pool.install before firstBlock signed) (messages reason) (failureMessage reason)) ∧
    (∀ (E : Type) (program : @CCalls.Events.Program (cInterface (pool.addresses firstBlock)) E),
      @CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) E program =
        LiteralPreparation.program model sigs →
      @QuietExecutionContract source E (cInterface (pool.addresses firstBlock)) model program
        (pool.install before firstBlock signed) ∧
      ∀ reason, @SilentExecutionContract E (cInterface (pool.addresses firstBlock)) reason program
        (pool.install before firstBlock signed)) ∧
    (∀ program : @CCalls.Events.Program (cInterface (pool.addresses firstBlock)) Invocation,
      @CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) Invocation program =
        LiteralPreparation.program model sigs →
      ∀ reason, @FailureExecutionContract (cInterface (pool.addresses firstBlock)) reason program
        category (messages reason) (pool.install before firstBlock signed) signed)

theorem failure_message_collected (model : Solve.FMI3Model source) (reason : GetFailure) :
    failureMessage reason ∈ functionTexts (Runtime.function model (signature false)) := by
  cases reason <;> simp [failureMessage, Runtime.function, Runtime.body, signature,
    Runtime.getFloat64, Runtime.require, Runtime.instancePrefix, Runtime.reject, Runtime.branch, Runtime.fail,
    Runtime.ret, Runtime.countLoop, Runtime.negate, Runtime.call, Runtime.v, Runtime.n,
    functionTexts, statementTexts, expressionTexts]

theorem prepared_correct (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature false ∈ sigs) (fresh : LiteralPreparation.KernelNamesFresh sigs)
    {pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare model sigs = some pool) : PreparedContract model sigs pool := by
  intro before firstBlock signed
  obtain ⟨category, categoryBound⟩ := LiteralPreparation.text_bound model sigs made Runtime.helpers[0]
    (List.mem_append_left _ (by simp [Runtime.helpers])) "logStatus" Logging.category_collected firstBlock
  have each : ∀ reason, ∃ message, pool.addresses firstBlock (failureMessage reason) = some message := by
    intro reason
    exact LiteralPreparation.message_bound model sigs made (signature false) member
      (failureMessage reason) (failure_message_collected model reason) firstBlock
  choose messages bound using each
  have categoryStored := pool.storage_valid before firstBlock signed "logStatus" category categoryBound
  have messageStored := fun reason => pool.storage_valid before firstBlock signed _ (messages reason) (bound reason)
  refine ⟨category, messages, categoryBound, categoryStored,
    fun reason => ⟨bound reason, messageStored reason⟩, ?_, ?_⟩
  · intro E program same
    have defined : (@CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) E program).definitions
        (signature false).name = some (.tree (Runtime.function model (signature false))) := by
      rw [same]
      exact LiteralPreparation.function_bound model sigs unique (signature false) member
    have helper : (@CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) E program).definitions
        "fail" = some (.tree Runtime.helpers[0]) := by
      rw [same]
      exact LiteralPreparation.helpers_bound model sigs Runtime.helpers[0] (by simp [Runtime.helpers])
    refine ⟨quiet_execution_correct (static := ⟨pool.addresses firstBlock⟩) model program _ defined ?_ ?_ ?_,
      fun reason => silent_execution_correct (static := ⟨pool.addresses firstBlock⟩) model reason program
        _ _ defined helper (bound reason)⟩
    · rw [same]
      exact LiteralPreparation.helpers_bound model sigs Runtime.helpers[1] (by simp [Runtime.helpers])
    · rw [same]
      exact LiteralPreparation.numerical_bound model sigs fresh .rhs
    · rw [same]
      exact LiteralPreparation.numerical_program model sigs
  · intro program same reason
    apply failure_execution_correct (static := ⟨pool.addresses firstBlock⟩) model reason program
      category (messages reason) _ signed _ _ categoryBound (bound reason) categoryStored (messageStored reason)
    · rw [same]
      exact LiteralPreparation.function_bound model sigs unique (signature false) member
    · rw [same]
      exact LiteralPreparation.helpers_bound model sigs Runtime.helpers[0] (by simp [Runtime.helpers])

structure FunctionContract (model : Solve.FMI3Model source) (sigs : List Signature) (text helper : String) : Prop where
  member : signature false ∈ sigs
  printed : text = (Runtime.function model (signature false)).render
  tokenization : Printer.FunctionTokenization RuntimePrinter.typedefs text (Runtime.function model (signature false))
  numerical : ModelRhs.FunctionContract model sigs helper
  prepared : ∀ pool, LiteralPreparation.prepare model sigs = some pool → PreparedContract model sigs pool

theorem rendered_contract (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature false ∈ sigs) (fresh : LiteralPreparation.KernelNamesFresh sigs) :
    FunctionContract model sigs (Runtime.function model (signature false)).render Runtime.helpers[1].render := by
  refine ⟨member, rfl, ?_, ModelRhs.rendered_contract model sigs fresh,
    fun _ made => prepared_correct model sigs unique member fresh made⟩
  apply RuntimePrinter.function_tokenization
  refine ⟨Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)),
    by decide +kernel, ?_⟩
  intro param member
  simp only [signature, List.mem_cons, List.not_mem_nil, or_false, Bool.false_eq_true, ↓reduceIte] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨?_, by decide +kernel⟩
  all_goals first
    | exact Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel))
    | exact Syntax.TypeSpelling.const
        (show Syntax.TypeSpelling RuntimePrinter.typedefs "fmi3ValueReference" from
          Syntax.TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)))

end Rumoca.FMI3.Float64Calls

noncomputable section
namespace Rumoca.FMI3.Float64Calls
open CMemory
variable [interface : CInterface]

/-- The complete public query stores the requested semantic values in request
order, including duplicates, and preserves all memory outside its output range.
The original represented model and time are retained under the stated ownership
conditions. No source trajectory or initialization policy is assumed here. -/
theorem QuietExecutionContract.get_refines (contract : QuietExecutionContract model program heap)
    (p input buffer : Address) (n : UInt64) (shape : Tensor.Shape)
    (references : Nat → UInt32) (kind : Kind) (mode : Mode)
    (state : ModelExchange.State) (time : Binary64.Value)
    (volume : shape.volume = n.toNat)
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
    (timeSeparate : ∀ i < shape.volume, p.member "time" ≠ buffer.index i) :
    ∃ after,
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling (signature false).name (arguments (some p) (some input) (some buffer) n n) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, after⟩) ∧
      (∀ i < shape.volume,
        load after (buffer.index i) = some (.finite ((selectReference (references i)).value model state time))) ∧
      (∀ address, (∀ i < shape.volume, address ≠ buffer.index i) → after address = heap address) ∧
      StateProofs.Represents after p state ∧
      load after (p.member "time") = some (.finite time) := by
  let outputs := outputValues model state time shape (fun i => selectReference (references i))
  refine ⟨TensorView.written heap buffer outputs shape.volume,
    contract.get p input buffer n shape references kind mode state time volume hk hm allowed readable valid
      writable referencesSeparate stateStored stateSeparate timeStored timeSeparate, ?_, ?_, ?_, ?_⟩
  · intro i inside
    have loaded := TensorView.written_reads heap buffer outputs ⟨i, inside⟩
    change load (TensorView.written heap buffer outputs shape.volume) (buffer.index i) =
      some (.finite outputs[i]) at loaded
    simpa only [outputs, outputValues_at] using loaded
  · intro address outside
    exact TensorView.written_frame heap buffer outputs shape.volume address outside
  · exact state_written heap buffer p outputs state shape.volume stateStored stateSeparate
  · exact time_written heap buffer p outputs time shape.volume timeStored timeSeparate

omit interface in
/-- The independently interpreted XML declaration is selected by the numeric
reference used by C, irrespective of XML declaration order or query duplicates. -/
theorem metadata_selection (model : Solve.FMI3Model source) (root : XML.Element)
    (metadata : ∀ selected, Float64Metadata.Lookup root selected.code (Float64Metadata.name model selected))
    (reference : UInt32) (valid : reference.toNat ≤ 2) :
    Float64Metadata.Lookup root reference.toNat
      (Float64Metadata.name model (selectReference reference)) := by
  have selected := metadata (selectReference reference)
  rw [selectReference_correct reference valid] at selected
  exact selected

end Rumoca.FMI3.Float64Calls
