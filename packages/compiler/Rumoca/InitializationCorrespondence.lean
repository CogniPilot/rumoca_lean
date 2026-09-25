import Rumoca.FMI3BuildProofs
import Rumoca.FMI3StaticLifecycle
import Rumoca.FMI3ResetProofs
import Rumoca.FMI3InitializationSemantics
import Rumoca.ArrayProofs
import Rumoca.TensorProduction
import Rumoca.ConstantProofs
import Rumoca.ConstantProduction
import RumocaFMI3.TensorReset
import RumocaFMI3.ConstantInstanceInit

/-! Cross-standard initialization correspondence for the admitted FMI 3 source
families. Each theorem composes, for one family, the MLS 3.7 §8.6 source
initialization relation, the FMI 3 initialization behavior of the emitted
adapter functions and the actual-artifact source-build contract that the fixed
checker proves for the emitted bytes.

* `integrator_initialization`: the unmodified scalar `Real` leaves its initial
  value free. The compiler selects the fallback start `0` as fixed and records
  both §8.6 notices. Factory creation and reset store that completed default,
  and exit from initialization mode, after any finite host write the adapter
  accepts, stores a source initialization with a unique completed trajectory.
* `tensorSquare_initialization`: `each start=0, each fixed=true` makes the zero
  state the source initialization. Factory creation and reset store the zero
  fill, and the enter/exit initialization-mode transitions preserve it.
* `constantRates_initialization`: every declared state initializes at `+0`.
  Factory creation and reset store the zero fill, and the initialization-mode
  transitions preserve it.

The tensor and constant theorems cover the default initialization. A finite
host write to the state in the Instantiated or Initialization mode is not
related to their source relations, which fix the start value. -/
noncomputable section
namespace Rumoca.InitializationCorrespondence
open CMemory CMemory.TensorView Rumoca.FMI3

private theorem value_zero : Binary64.value Binary64.positiveZero = 0 := by
  have units : Binary64.units Binary64.positiveZero = 0 := by decide +kernel
  simp only [Binary64.value, units, Int.cast_zero, zero_div]

/-- The enter/exit initialization-mode transitions write only the mode member,
so every state-region reading survives them. -/
theorem writeMode_reads {shape : Tensor.Shape} (heap : Heap) (p : Address) (mode : Mode)
    (v : Values shape) (reads : Reads heap (p.member TensorInstance.stateName) v) :
    Reads (LifecycleBodies.writeMode heap p mode) (p.member TensorInstance.stateName) v := by
  intro i
  have frame := LifecycleBodies.write_frame heap p ((p.member TensorInstance.stateName).index i.val) mode
    (TensorReset.region_ne_member p TensorInstance.stateName "mode" (by decide) i.val)
  simp only [load, frame]
  exact reads i

/-! ### Scalar Integrator -/

/-- The scalar Integrator family. For every compiled unit source whose emitted
bytes satisfy the source-build contract:

1. MLS §8.6: the completed Solve plan records the fallback and the inferred
   fixing, and its default is a source initialization with a unique trajectory;
2. every finite start value is a source initialization, so a host-selected
   start is admissible;
3. the actual adapter satisfies the adapter contract, whose factory, reset and
   initialization-mode bodies execute the following behavior;
4. static factory creation and reset store the completed default;
5. exiting initialization mode from any represented state, including one
   written by the host, stores a source initialization of the supplied start
   time whose completed trajectory is unique. -/
theorem integrator_initialization (compiled : compile input = .ok a)
    (build : SourceBuildContract a c description adapter metadata) (t₀ : ℝ) :
    compile input = .ok a ∧
    Initialization.Notice.fallbackUsed ∈ a.solve.initial.notices ∧
    Initialization.Notice.unfixedStartSelected ∈ a.solve.initial.notices ∧
    Source.Initializes a.parsed.ast t₀ (Initialization.trajectory t₀ (a.solve.initial.initial : ℝ)) ∧
    (∀ x, Source.Initializes a.parsed.ast t₀ x → x t₀ = (a.solve.initial.initial : ℝ) →
      x = Initialization.trajectory t₀ (a.solve.initial.initial : ℝ)) ∧
    (∀ start : Binary64.Value,
      Source.Initializes a.parsed.ast t₀ (Initialization.trajectory t₀ (Binary64.value start))) ∧
    AdapterContract a adapter ∧
    (∀ {capacity : Nat} (heap : Heap) (base : Address) (block : Nat)
      (owners : SlotOwners.State capacity) (slot : Fin capacity) (owner : Nat) (kind : Kind)
      (environment logger : Option Address) (logging : Bool),
      StaticFactory.Created heap base block owners slot owner kind environment logger logging →
      ∃ initial : Binary64.Value,
        load heap (StateProofs.stateAddress (base.index slot.val)) = some (.finite initial) ∧
        Binary64.value initial = (a.solve.initial.initial : ℝ) ∧
        Source.Initializes a.parsed.ast t₀ (Initialization.trajectory t₀ (Binary64.value initial))) ∧
    (∀ (heap : Heap) (p : Address), ResetSourceResult a p ⟨.integer 0, Reset.finalHeap heap p⟩ t₀) ∧
    (∀ (heap : Heap) (p : Address) (args : Initialization.Arguments) (kind : Kind)
      (state : ModelExchange.State), StateProofs.Represents heap p state →
      InitializationCalls.SourceInitialized a.parsed.ast (InitializationCalls.exitedHeap heap p args kind) p args.start
        (Initialization.trajectory (Binary64.value args.start) (Binary64.value state.x)) ∧
      ∀ candidate, InitializationCalls.SourceInitialized a.parsed.ast (InitializationCalls.exitedHeap heap p args kind) p
          args.start candidate →
        candidate = Initialization.trajectory (Binary64.value args.start) (Binary64.value state.x)) := by
  obtain ⟨source, fallback, unfixed⟩ := a.solve.initialization_correct t₀
  refine ⟨compiled, fallback, unfixed, source, a.solve.initialized_solution_unique t₀,
    fun start => ⟨a.solve.dae.flat.resolved, Initialization.unfixed_start_is_free none _ _⟩,
    build.adapter, ?_, fun heap p => reset_result a heap p t₀, ?_⟩
  · intro _ heap base block owners slot owner kind environment logger logging created
    obtain ⟨initial, loaded, agreement, initializes, _⟩ := created.source_default a t₀
    exact ⟨initial, loaded, agreement, initializes⟩
  · intro heap p args kind state represented
    have exited := InitializationCalls.exited_source_initialized a.solve.prepareFMI3 heap p args kind
      state represented
    exact ⟨exited, fun candidate other => InitializationCalls.source_initialized_unique other
      (InitializationBodies.exit_model (InitializationEntry.model represented args) kind)⟩

/-! ### TensorSquare -/

/-- The Real reading of a finite binary64 tensor. -/
def realValues {shape : Tensor.Shape} (v : Values shape) : Tensor.Value ℝ shape :=
  ⟨Vector.ofFn fun i => Binary64.value v[i]⟩

theorem realValues_get {shape : Tensor.Shape} (v : Values shape) (i : Fin shape.volume) :
    (realValues v)[i] = Binary64.value v[i] := by
  change (Vector.ofFn fun i : Fin shape.volume => Binary64.value v[i])[i.val] = Binary64.value v[i]
  rw [Vector.getElem_ofFn]

/-- The state region at `base` reads a finite tensor whose Real reading satisfies
the source initialization relation and the prepared kernel's initial condition. -/
def TensorStateInitial (a : TensorArtifact input) (heap : Heap) (base : Address) : Prop :=
  ∃ v : Values ArrayProfile.stateShape, Reads heap base v ∧
    a.prepared.parsed.parsed.ast.Initial (fun _ i => Binary64.value v[i]) ∧
    a.prepared.kernel.Initial (realValues v)

/-- The binary64 zero fill is the tensor source initialization. -/
theorem tensor_zero_initial (a : TensorArtifact input) (heap : Heap) (base : Address)
    (reads : Reads heap base (TensorReset.zeroValues ArrayProfile.stateShape)) :
    TensorStateInitial a heap base := by
  have source : a.prepared.parsed.parsed.ast.Initial
      (fun _ i => Binary64.value (TensorReset.zeroValues ArrayProfile.stateShape)[i]) := by
    funext i
    simp [TensorReset.zeroValues, value_zero]
  refine ⟨_, reads, source, ?_⟩
  have chain := (a.prepared.initialization_correct
    (fun _ => realValues (TensorReset.zeroValues ArrayProfile.stateShape))).mp
  apply chain
  convert source using 3
  exact realValues_get _ _

/-- The TensorSquare family. For every tensor artifact whose emitted bytes satisfy
the tensor source-build contract, the actual adapter satisfies the tensor adapter
contract, whose factory terminates in `TensorInstanceInit.finalHeap`, whose reset
terminates in `TensorReset.restoreHeap` over the record regions and whose initialization-mode transitions
terminate in `LifecycleBodies.writeMode`. Each of those heaps holds a state that
satisfies the MLS §8.6 source initialization (`each start=0, each fixed=true`)
and the prepared kernel's initial condition. -/
theorem tensorSquare_initialization (a : TensorArtifact input)
    (build : TensorSourceBuildContract a modelC buildDescription adapter metadata) :
    (∃ (src : AST.Model) (w : Solve.FMI3Model src), src.name = a.name ∧
      ∀ [StaticLiterals], TensorAdapter.Contract w a.tensorModel adapter) ∧
    (∀ (heap : Heap) (p : Address) (slot : Nat) (kind : Kind) (environment logger : Option Address)
      (logging : Bool),
      TensorStateInitial a
        (TensorInstanceInit.finalHeap heap p slot kind environment logger logging
          (TensorStorage.regions ArrayProfile.stateShape true a.tensorModel.hasOutput))
        (p.member TensorInstance.stateName)) ∧
    (∀ (heap : Heap) (p : Address),
      TensorStateInitial a
        (TensorReset.restoreHeap heap p (TensorStorage.regions ArrayProfile.stateShape true a.tensorModel.hasOutput))
        (p.member TensorInstance.stateName)) ∧
    (∀ (heap : Heap) (p : Address) (mode : Mode),
      TensorStateInitial a heap (p.member TensorInstance.stateName) →
      TensorStateInitial a (LifecycleBodies.writeMode heap p mode) (p.member TensorInstance.stateName)) :=
  ⟨build.adapter,
    fun heap p slot kind environment logger logging => tensor_zero_initial a _ _
      (TensorReset.restoreHeap_reads _ p _ (TensorStorage.regions_distinct _ true _)
        (TensorInstance.stateName, ArrayProfile.stateShape) (by simp [TensorStorage.regions])),
    fun heap p => tensor_zero_initial a _ _
      (TensorReset.restoreHeap_reads heap p _ (TensorStorage.regions_distinct _ true _)
        (TensorInstance.stateName, ArrayProfile.stateShape) (by simp [TensorStorage.regions])),
    fun heap p mode ⟨v, reads, source, kernel⟩ => ⟨v, writeMode_reads heap p mode v reads, source, kernel⟩⟩

/-! ### ConstantRates -/

/-- The state region at `base` reads a finite vector whose declaration-order
entries are the prepared initial values, and every named reading of it
satisfies the source initialization relation. -/
def ConstantStateInitial (a : ConstantArtifact input) (heap : Heap) (base : Address) : Prop :=
  ∃ v : Values a.constantModel.shape, Reads heap base v ∧
    ∀ values : String → Binary64.Value,
      (∀ i : Fin a.prepared.parsed.parsed.ast.states.length,
        values (a.prepared.parsed.parsed.ast.states.get i) =
          v[i.val]'(by rw [a.constantModel.shape_volume]; exact i.isLt)) →
      a.prepared.parsed.parsed.ast.Initial values

/-- The binary64 zero fill is the constant-rate source initialization. -/
theorem constant_zero_initial (a : ConstantArtifact input) (heap : Heap) (base : Address)
    (reads : Reads heap base (TensorReset.zeroValues a.constantModel.shape)) :
    ConstantStateInitial a heap base := by
  refine ⟨_, reads, fun values named => ?_⟩
  apply (a.prepared.initialization_correct values).mpr
  intro i
  rw [named i, a.prepared.ivp_lowered]
  simp [TensorReset.zeroValues, ConstantProfile.ConstantIVP.initial]

/-- The ConstantRates family. For every constant artifact whose emitted bytes
satisfy the constant source-build contract, the actual adapter satisfies the
constant adapter contract, whose factory, reset and initialization-mode bodies
are the shared tensor bodies at the constant state shape. Each of their final
heaps holds a state satisfying the source initialization relation. -/
theorem constantRates_initialization (a : ConstantArtifact input)
    (build : ConstantSourceBuildContract a modelC buildDescription adapter metadata) :
    (∃ (src : AST.Model) (w : Solve.FMI3Model src), src.name = a.name ∧
      ∀ [StaticLiterals], ConstantAdapter.Contract w a.constantModel adapter) ∧
    (∀ (heap : Heap) (p : Address) (slot : Nat) (kind : Kind) (environment logger : Option Address)
      (logging : Bool),
      ConstantStateInitial a
        (TensorInstanceInit.finalHeap heap p slot kind environment logger logging
          (ConstantInstanceInit.regions a.constantModel.shape))
        (p.member TensorInstance.stateName)) ∧
    (∀ (heap : Heap) (p : Address),
      ConstantStateInitial a
        (TensorReset.restoreHeap heap p (ConstantInstanceInit.regions a.constantModel.shape))
        (p.member TensorInstance.stateName)) ∧
    (∀ (heap : Heap) (p : Address) (mode : Mode),
      ConstantStateInitial a heap (p.member TensorInstance.stateName) →
      ConstantStateInitial a (LifecycleBodies.writeMode heap p mode) (p.member TensorInstance.stateName)) :=
  ⟨build.adapter,
    fun heap p slot kind environment logger logging => constant_zero_initial a _ _
      (ConstantInstanceInit.reads_state heap p slot kind environment logger logging _),
    fun heap p => constant_zero_initial a _ _
      (TensorReset.restoreHeap_reads heap p _ (TensorStorage.regions_distinct _ false false)
        (TensorInstance.stateName, a.constantModel.shape)
        (by simp [TensorStorage.regions])),
    fun heap p mode ⟨v, reads, source⟩ => ⟨v, writeMode_reads heap p mode v reads, source⟩⟩

end Rumoca.InitializationCorrespondence
