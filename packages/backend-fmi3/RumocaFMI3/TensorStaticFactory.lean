import RumocaFMI3.TensorInstanceInit
import RumocaFMI3.StaticFactoryExhaustion
import RumocaFMI3.StaticRelease
import RumocaFMI3.FactoryValidation

/-! Tensor instance-creation reservation suffix over the static tensor pool.

The tensor factory shares the model-agnostic reservation prefix of the scalar
factory: a bounded serial slot reservation with the atomic scan helper
(`CAtomicScan`), a capacity guard (`StaticFactory.guard`), and the reserved-array
element selection (`StaticFactory.selectInstance`). Only the reserved-record
initializer differs: instead of the scalar prepared-model initializer, the tensor
factory runs the reserved-record initializer `TensorInstanceInit.code`, which
zero-fills the state region with the tensor reset loop.

This file composes the reservation entry, the atomic scan, the capacity guard and
the tensor initializer into the successful-creation and exhaustion behaviors, at
the same reservation `Scope` premise level as the scalar `StaticFactory.successful`
(and its exhaustion counterpart). It reuses every model-agnostic reservation
lemma of the scalar factory (`StaticFactory.select_step`, `guard_step`, `reserve`,
`guard`, `selectInstance`, `reservedLocals`, `reservedTypes`, `ReservationBindings`)
and the shared atomic-scan machinery, adding no source case.

The production tensor dispatcher consumes this factory for its public instantiate
functions. This module alone is not a source-acceptance or actual-artifact
certificate. Every theorem is universal in the tensor shape and the pool index. -/
noncomputable section
namespace Rumoca.FMI3.TensorFactory
open CTree CMemory CBody
open Rumoca.FMI3.StaticFactory (reserve guard selectInstance reservedLocals reservedTypes
  ReservationBindings select_step guard_step)
variable [interface : CInterface]

/-- The tensor reserved-record initializer, prefixed by the reserved-array element
selection. Mirrors the scalar `StaticFactory.initializeInstance`. -/
def initializeInstance (shape : Tensor.Shape) (kind : Kind) : List Stmt :=
  selectInstance :: TensorInstanceInit.code shape kind

/-- The tensor creation reservation suffix: reserve a slot with the atomic scan,
guard capacity, then initialize the reserved record. Mirrors the scalar
`StaticFactory.code`. -/
def code (shape : Tensor.Shape) (kind : Kind) : List Stmt :=
  reserve :: guard :: initializeInstance shape kind

/-- The reservation scope: the scalar reservation bindings plus the freshness of
the initializer's own staged locals (`dst`, `expected`, `k`). -/
structure Scope (env : Locals) (base flags : Address) (capacity : Nat)
    (environment logger : Option Address) (logging : Bool) : Prop where
  instances : resolve env "rumoca_instances" = some (.pointer (some base))
  flagsBound : resolve env "rumoca_instance_flags" = some (.pointer (some flags))
  count : resolve env "rumoca_instance_capacity" = some (.integer capacity)
  instanceFresh : env "m" = none
  slotFresh : env "slot" = none
  helperFresh : env CAtomicScan.function.signature.name = none
  environmentBound : resolve env "instanceEnvironment" = some (.pointer environment)
  loggerBound : resolve env "logMessage" = some (.pointer logger)
  loggingBound : resolve env "loggingOn" = some (boolean logging)
  dstFresh : env "dst" = none
  expectedFresh : env "expected" = none
  counterFresh : env "k" = none

/-- Reduce the tensor scope to the model-agnostic scalar scope for reuse of the
shared reservation lemmas. -/
def Scope.toStatic {env base flags capacity environment logger logging}
    (scope : Scope env base flags capacity environment logger logging) :
    StaticFactory.Scope env base flags capacity environment logger logging :=
  ⟨scope.instances, scope.flagsBound, scope.count, scope.instanceFresh, scope.slotFresh,
    scope.helperFresh, scope.environmentBound, scope.loggerBound, scope.loggingBound⟩

/-! ### The reservation entry, the slot-index resume and the guarded initializer -/

/-- Enter the atomic reservation helper, saving the capacity guard and tensor
initializer as the caller continuation. Mirrors `StaticFactory.reserve_entry`. -/
theorem reserve_entry (program : CCalls.Events.Program E) (shape : Tensor.Shape) (kind : Kind)
    (env : Locals) (types : CLoops.Types) (heap : Heap) (base flags : Address) (capacity : Nat)
    (environment logger : Option Address) (logging : Bool) (stack : CCalls.Typed.Continuation)
    (scope : Scope env base flags capacity environment logger logging)
    (named : interface.constants CAtomicScan.function.signature.name = none) :
    CCalls.Events.internalNext program
      (.body (.running (code shape kind) env types heap) "fmi3Instance" stack) =
      some (.calling CAtomicScan.function.signature.name [.pointer (some flags), .integer capacity] heap
        (.caller (.declare "size_t" "slot") (guard :: initializeInstance shape kind) env types "fmi3Instance" stack)) := by
  exact CCalls.Events.named_declare_entry program env types heap "size_t" "slot"
    CAtomicScan.function.signature.name _ _ _ "fmi3Instance" stack scope.slotFresh scope.helperFresh named
    (by decide +kernel) (by simp [CCalls.arguments, CCalls.argumentsWith, legacyExpressions, eval, evalWith, scope.flagsBound, scope.count])

/-- Resume with the reserved slot index bound. Mirrors `StaticFactory.reserve_resume`. -/
theorem reserve_resume (program : CCalls.Events.Program E) (shape : Tensor.Shape) (kind : Kind)
    (env : Locals) (types : CLoops.Types) (heap : Heap) (slot : Nat) (stack : CCalls.Typed.Continuation)
    (fresh : env "slot" = none) (size : interface.types "size_t" = some .size) (bounded : slot < 2 ^ 64) :
    CCalls.Events.internalNext program
      (.returning (.integer slot) heap
        (.caller (.declare "size_t" "slot") (guard :: initializeInstance shape kind) env types "fmi3Instance" stack)) =
      some (.body (.running (guard :: initializeInstance shape kind) (reservedLocals env slot)
        (reservedTypes types) heap) "fmi3Instance" stack) :=
  CCalls.Events.declare_result program env types heap "size_t" "slot" _ "fmi3Instance" stack
    (.integer slot) (.integer slot) .size fresh size (CLoops.convert_size_nat slot bounded)

/-- Select the reserved array element and run the tensor record initializer to the
returned handle and initialized heap. Mirrors `StaticFactory.initialization_reaches`. -/
theorem initialization_reaches (program : CCalls.Events.Program E) (shape : Tensor.Shape) (kind : Kind)
    (env : Locals) (types : CLoops.Types) (heap : Heap) (base : Address) (capacity : Nat)
    (slot : Fin capacity) (environment logger : Option Address) (logging : Bool)
    (stack : CCalls.Typed.Continuation)
    (storage : TensorInstanceInit.Storage heap (base.index slot.val) shape)
    (bounded : slot.val < 2 ^ 64) (volumeBounded : shape.volume < 2 ^ 64)
    (instances : resolve env "rumoca_instances" = some (.pointer (some base)))
    (selected : resolve env "slot" = some (.integer slot.val)) (fresh : env "m" = none)
    (environmentBound : resolve env "instanceEnvironment" = some (.pointer environment))
    (loggerBound : resolve env "logMessage" = some (.pointer logger))
    (loggingBound : resolve env "loggingOn" = some (boolean logging))
    (dstFresh : env "dst" = none) (expectedFresh : env "expected" = none) (counterFresh : env "k" = none)
    (pointer : interface.types "Instance *" = some .pointer)
    (float : interface.types "fmi3Float64 *" = some .pointer)
    (size : interface.types "size_t" = some .size)
    (handle : interface.types "fmi3Instance" = some .pointer) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (initializeInstance shape kind) env types heap) "fmi3Instance" stack)
      (.returning (.pointer (some (base.index slot.val)))
        (TensorInstanceInit.finalHeap heap (base.index slot.val) slot.val kind environment logger logging shape)
        stack) := by
  refine .next (CCalls.Events.body_step program
    (select_step env types heap base slot.val (TensorInstanceInit.code shape kind) instances selected fresh pointer)
    "fmi3Instance" stack) ?_
  have binds : TensorInstanceInit.Bindings (CBody.bind env "m" (.pointer (some (base.index slot.val))))
      (base.index slot.val) slot.val environment logger logging :=
    ⟨by simp [resolve, CBody.bind], by simpa [resolve, CBody.bind] using selected,
      by simpa [resolve, CBody.bind] using environmentBound,
      by simpa [resolve, CBody.bind] using loggerBound,
      by simpa [resolve, CBody.bind] using loggingBound,
      by simpa [CBody.bind] using dstFresh, by simpa [CBody.bind] using expectedFresh,
      by simpa [CBody.bind] using counterFresh⟩
  exact TensorInstanceInit.return_reaches program shape kind
    (CBody.bind env "m" (.pointer (some (base.index slot.val)))) (CLoops.bindType types "m" .pointer)
    heap (base.index slot.val) slot.val environment logger logging stack storage binds bounded volumeBounded
    float size handle

/-- The capacity guard passes for a reserved slot, and the initializer runs. Mirrors
`StaticFactory.guarded_initialization`. -/
theorem guarded_initialization (program : CCalls.Events.Program E) (shape : Tensor.Shape) (kind : Kind)
    (env : Locals) (types : CLoops.Types) (heap : Heap) (base : Address) (capacity : Nat)
    (slot : Fin capacity) (environment logger : Option Address) (logging : Bool)
    (stack : CCalls.Typed.Continuation)
    (storage : TensorInstanceInit.Storage heap (base.index slot.val) shape)
    (bounded : slot.val < 2 ^ 64) (volumeBounded : shape.volume < 2 ^ 64)
    (instances : resolve env "rumoca_instances" = some (.pointer (some base)))
    (selected : resolve env "slot" = some (.integer slot.val))
    (count : resolve env "rumoca_instance_capacity" = some (.integer capacity)) (fresh : env "m" = none)
    (environmentBound : resolve env "instanceEnvironment" = some (.pointer environment))
    (loggerBound : resolve env "logMessage" = some (.pointer logger))
    (loggingBound : resolve env "loggingOn" = some (boolean logging))
    (dstFresh : env "dst" = none) (expectedFresh : env "expected" = none) (counterFresh : env "k" = none)
    (pointer : interface.types "Instance *" = some .pointer)
    (float : interface.types "fmi3Float64 *" = some .pointer)
    (size : interface.types "size_t" = some .size)
    (handle : interface.types "fmi3Instance" = some .pointer) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (guard :: initializeInstance shape kind) env types heap) "fmi3Instance" stack)
      (.returning (.pointer (some (base.index slot.val)))
        (TensorInstanceInit.finalHeap heap (base.index slot.val) slot.val kind environment logger logging shape)
        stack) := by
  have different : slot.val ≠ capacity := Nat.ne_of_lt slot.isLt
  have first := guard_step env types heap slot.val capacity (initializeInstance shape kind) selected count
  simp only [different, ↓reduceIte, List.nil_append] at first
  exact .next (CCalls.Events.body_step program first "fmi3Instance" stack)
    (initialization_reaches program shape kind env types heap base capacity slot environment logger logging
      stack storage bounded volumeBounded instances selected fresh environmentBound loggerBound loggingBound
      dstFresh expectedFresh counterFresh pointer float size handle)

/-! ### Successful creation and exhaustion at the reservation scope -/

/-- Successful creation returns a handle to a slot that was free and performs
the scan's bounded atomic work. Initialization changes exactly that record and
preserves other cells relative to the post-scan heap; reservation itself changes
the selected atomic flag. Mirrors `StaticFactory.successful` at the same `Scope`
premise level. -/
theorem successful (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (shape : Tensor.Shape) (kind : Kind) (env : Locals) (types : CLoops.Types) (before after : Heap)
    (base flags : Address) (capacity : Nat) (environment logger : Option Address) (logging : Bool)
    (scope : Scope env base flags capacity environment logger logging)
    (storage : ∀ slot : Fin capacity, TensorInstanceInit.Storage before (base.index slot.val) shape)
    (boolean : interface.types "_Bool" = some .boolean)
    (atomicPointer : interface.types "volatile atomic_bool *" = some .pointer)
    (size : interface.types "size_t" = some .size)
    (constantSize : interface.types "const size_t" = some .size)
    (pointer : interface.types "Instance *" = some .pointer)
    (float : interface.types "fmi3Float64 *" = some .pointer)
    (handle : interface.types "fmi3Instance" = some .pointer)
    (namedHelper : interface.constants CAtomicScan.function.signature.name = none)
    (namedAtomic : interface.constants "atomic_exchange" = none)
    (atomicBound : program.externals "atomic_exchange" =
      some (CAtomicBoolean.Calls.exchangeExternal tag boolean))
    (defined : program.internal.definitions CAtomicScan.function.signature.name =
      some (.tree CAtomicScan.function))
    (bounded : capacity < 2 ^ 64) (volumeBounded : shape.volume < 2 ^ 64)
    (outcome : CAtomicScan.Outcome flags capacity 0 before trace slot after) (inside : slot < capacity) :
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.body (.running (code shape kind) env types before) "fmi3Instance" .done) behavior ↔
      behavior = .terminates (trace.map tag) ⟨.pointer (some (base.index slot)),
        TensorInstanceInit.finalHeap after (base.index slot) slot kind environment logger logging shape⟩ := by
  have ready := (storage ⟨slot, inside⟩).preserved (CAtomicScan.outcome_storage outcome).1
  have initialized := guarded_initialization program shape kind (reservedLocals env slot)
    (reservedTypes types) after base capacity ⟨slot, inside⟩ environment logger logging .done ready
    (by omega) volumeBounded
    (by simpa [reservedLocals, resolve, CBody.bind] using scope.instances)
    (by simp [reservedLocals, resolve, CBody.bind])
    (by simpa [reservedLocals, resolve, CBody.bind] using scope.count)
    (by simpa [reservedLocals, CBody.bind] using scope.instanceFresh)
    (by simpa [reservedLocals, resolve, CBody.bind] using scope.environmentBound)
    (by simpa [reservedLocals, resolve, CBody.bind] using scope.loggerBound)
    (by simpa [reservedLocals, resolve, CBody.bind] using scope.loggingBound)
    (by simpa [reservedLocals, CBody.bind] using scope.dstFresh)
    (by simpa [reservedLocals, CBody.bind] using scope.expectedFresh)
    (by simpa [reservedLocals, CBody.bind] using scope.counterFresh)
    pointer float size handle
  have returned := CCalls.Events.internal_prefix program
    (.next (reserve_resume program shape kind env types after slot .done scope.slotFresh size
      (by omega)) initialized)
    (CCalls.Events.return_forced program (.pointer (some (base.index slot)))
      (TensorInstanceInit.finalHeap after (base.index slot) slot kind environment logger logging shape))
  have called := CAtomicScan.call_prefix program tag boolean atomicPointer size constantSize namedAtomic
    atomicBound defined bounded outcome _ returned
  have complete := CCalls.Events.internal_prefix program
    (.next (reserve_entry program shape kind env types before base flags capacity environment logger logging
      .done scope namedHelper) (.refl _)) called
  simpa only [List.append_nil] using complete.behaviors

/-- The reservation reaches the shared exhaustion rejection when the scan returns
the capacity sentinel. Mirrors `StaticFactory.exhaustion_path`. -/
theorem exhaustion_path (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (shape : Tensor.Shape) (kind : Kind) (env : Locals) (types : CLoops.Types) (before after : Heap)
    (base flags : Address) (capacity : Nat) (environment logger : Option Address) (logging : Bool)
    (scope : Scope env base flags capacity environment logger logging)
    (bindings : ReservationBindings program tag) (bounded : capacity < 2 ^ 64)
    (outcome : CAtomicScan.Outcome flags capacity 0 before trace capacity after)
    (stack : CCalls.Typed.Continuation) :
    Transition.Events.Prefix (CCalls.Events.machine program)
      (.body (.running (code shape kind) env types before) "fmi3Instance" stack)
      (trace.map tag)
      (.body (.running (FactoryRejection.code "Instance capacity exhausted" ++ initializeInstance shape kind)
        (reservedLocals env capacity) (reservedTypes types) before) "fmi3Instance" stack) := by
  have unchanged := (CAtomicScan.outcome_exhausted outcome rfl).1
  subst after
  apply (CCalls.Events.internal_path program
    (.next (reserve_entry program shape kind env types before base flags capacity environment logger logging
      stack scope bindings.namedHelper) (.refl _))).trans
  refine (List.append_nil (trace.map tag)) ▸
    (CAtomicScan.call_path program tag bindings.boolean bindings.atomicPointer bindings.size
      bindings.constantSize bindings.namedAtomic bindings.atomicBound bindings.defined bounded outcome _).trans ?_
  apply CCalls.Events.internal_path program
  refine .next (reserve_resume program shape kind env types before capacity stack scope.slotFresh
    bindings.size bounded) ?_
  have guarded := guard_step (reservedLocals env capacity) (reservedTypes types) before capacity capacity
    (initializeInstance shape kind)
    (by simp [reservedLocals, resolve, CBody.bind])
    (by simpa [reservedLocals, resolve, CBody.bind] using scope.count)
  simp only [↓reduceIte] at guarded
  exact .next (CCalls.Events.body_step program guarded "fmi3Instance" stack) (.refl _)

/-- With logging disabled or absent, exhaustion returns null, preserves the whole
heap, and performs only the scan's bounded atomic work. Mirrors
`StaticFactory.exhausted_silent`. -/
theorem exhausted_silent (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (shape : Tensor.Shape) (kind : Kind) (env : Locals) (types : CLoops.Types) (before after : Heap)
    (base flags : Address) (capacity : Nat) (environment logger : Option Address) (logging : Bool)
    (scope : Scope env base flags capacity environment logger logging)
    (bindings : ReservationBindings program tag) (bounded : capacity < 2 ^ 64)
    (outcome : CAtomicScan.Outcome flags capacity 0 before trace capacity after)
    (handle : interface.types "fmi3Instance" = some .pointer)
    (nullBound : resolve env "NULL" = some (.pointer none))
    (quiet : (logger.isSome && logging) = false) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.body (.running (code shape kind) env types before) "fmi3Instance" .done) behavior ↔
      behavior = .terminates (trace.map tag) ⟨.pointer none, before⟩ := by
  have path := exhaustion_path program tag shape kind env types before after base flags capacity
    environment logger logging scope bindings bounded outcome .done
  have dispatched := FactoryRejection.dispatch program "Instance capacity exhausted"
    (reservedLocals env capacity) (reservedTypes types) before (initializeInstance shape kind) .done logger logging
    (by simpa [reservedLocals, resolve, CBody.bind] using scope.loggerBound)
    (by simpa [reservedLocals, resolve, CBody.bind] using scope.loggingBound)
  rw [quiet] at dispatched
  simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append] at dispatched
  have finished := CCalls.Events.internal_prefix program (.next dispatched
    (FactoryRejection.return_null program (reservedLocals env capacity) (reservedTypes types) before
      (initializeInstance shape kind) .done
      (by simpa [reservedLocals, resolve, CBody.bind] using nullBound) handle))
    (CCalls.Events.return_forced program (.pointer none) before)
  simpa only [List.append_nil] using (path.forced finished).behaviors behavior

/-! ### Ownership: the created slot is marked owned and can be released -/

/-- The initializer preserves every slot lease of the reservation-flag block: it
only writes the reserved record's own cells, never an atomic flag. -/
theorem initialized_owners (program : CCalls.Events.Program E) (shape : Tensor.Shape) (kind : Kind)
    (env : Locals) (types : CLoops.Types) (heap : Heap) (base : Address) (capacity : Nat)
    (slot : Fin capacity) (environment logger : Option Address) (logging : Bool) (block : Nat)
    (owners : SlotOwners.State capacity)
    (storage : TensorInstanceInit.Storage heap (base.index slot.val) shape)
    (bounded : slot.val < 2 ^ 64) (volumeBounded : shape.volume < 2 ^ 64)
    (instances : resolve env "rumoca_instances" = some (.pointer (some base)))
    (selected : resolve env "slot" = some (.integer slot.val)) (fresh : env "m" = none)
    (environmentBound : resolve env "instanceEnvironment" = some (.pointer environment))
    (loggerBound : resolve env "logMessage" = some (.pointer logger))
    (loggingBound : resolve env "loggingOn" = some (boolean logging))
    (dstFresh : env "dst" = none) (expectedFresh : env "expected" = none) (counterFresh : env "k" = none)
    (pointer : interface.types "Instance *" = some .pointer)
    (float : interface.types "fmi3Float64 *" = some .pointer)
    (size : interface.types "size_t" = some .size)
    (handle : interface.types "fmi3Instance" = some .pointer)
    (represented : SlotOwners.Represents block heap owners) :
    SlotOwners.Represents block
      (TensorInstanceInit.finalHeap heap (base.index slot.val) slot.val kind environment logger logging shape)
      owners := by
  have path := initialization_reaches program shape kind env types heap base capacity slot environment logger
    logging .done storage bounded volumeBounded instances selected fresh environmentBound loggerBound
    loggingBound dstFresh expectedFresh counterFresh pointer float size handle
  suffices h : ∀ s t, Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t) s t →
      SlotOwners.Represents block (CReadOnly.typedHeap s) owners →
      SlotOwners.Represents block (CReadOnly.typedHeap t) owners by
    simpa [CReadOnly.typedHeap, CReadOnly.loopHeap] using
      h _ _ path (by simpa [CReadOnly.typedHeap, CReadOnly.loopHeap] using represented)
  intro s t reached hs
  induction reached with
  | refl => exact hs
  | next first _ ih => exact ih (SlotOwners.internal_preserves hs program first)

/-- The postcondition of a successful creation: the reserved record is
initialized, the created slot is represented in the flag block and owned. -/
structure Created (after : Heap) (base : Address) (block : Nat) (owners : SlotOwners.State capacity)
    (slot : Fin capacity) (owner : Nat) (kind : Kind) (environment logger : Option Address)
    (logging : Bool) (shape : Tensor.Shape) : Prop where
  initialized : TensorInstanceInit.Initialized after (base.index slot.val) slot.val kind
    environment logger logging shape
  represented : SlotOwners.Represents block
    (TensorInstanceInit.finalHeap after (base.index slot.val) slot.val kind environment logger logging shape)
    owners
  owned : owners slot = some owner

/-- Successful creation reserves the free slot, marks it owned in the flag block,
and returns the initialized handle. Mirrors `StaticFactory.successful_owned`. -/
theorem successful_owned (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (shape : Tensor.Shape) (kind : Kind) (env : Locals) (types : CLoops.Types) (before after : Heap)
    (base : Address) (block capacity : Nat) (environment logger : Option Address) (logging : Bool)
    (scope : Scope env base ⟨block, [], 0⟩ capacity environment logger logging)
    (storage : ∀ slot : Fin capacity, TensorInstanceInit.Storage before (base.index slot.val) shape)
    (bindings : ReservationBindings program tag)
    (pointer : interface.types "Instance *" = some .pointer)
    (float : interface.types "fmi3Float64 *" = some .pointer)
    (handle : interface.types "fmi3Instance" = some .pointer)
    (bounded : capacity < 2 ^ 64) (volumeBounded : shape.volume < 2 ^ 64)
    (owners : SlotOwners.State capacity) (represented : SlotOwners.Represents block before owners)
    (owner : Nat) (slot : Fin capacity)
    (outcome : CAtomicScan.Outcome ⟨block, [], 0⟩ capacity 0 before trace slot.val after) :
    let live := TensorInstanceInit.finalHeap after (base.index slot.val) slot.val kind environment logger
      logging shape
    SlotOwners.reserve owners slot owner = some (SlotOwners.update owners slot (some owner)) ∧
      Created after base block (SlotOwners.update owners slot (some owner)) slot owner kind
        environment logger logging shape ∧
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.body (.running (code shape kind) env types before) "fmi3Instance" .done) behavior ↔
        behavior = .terminates (trace.map tag) ⟨.pointer (some (base.index slot.val)), live⟩) := by
  have effect := CAtomicScan.outcome_reserved outcome slot.isLt
  have exchanged : CAtomicBoolean.exchange before (AtomicSlots.address block slot) true = some (false, after) :=
    CAtomicBoolean.exchange_iff.mpr (by simpa [Address.index, AtomicSlots.address] using effect)
  have reserved := SlotOwners.exchange_reserves represented exchanged owner
  have ready := (storage slot).preserved (CAtomicScan.outcome_storage outcome).1
  have bounded' : slot.val < 2 ^ 64 := Nat.lt_trans slot.isLt bounded
  have owned := initialized_owners program shape kind (reservedLocals env slot.val) (reservedTypes types) after
    base capacity slot environment logger logging block (SlotOwners.update owners slot (some owner)) ready
    bounded' volumeBounded
    (by simpa [reservedLocals, resolve, CBody.bind] using scope.instances)
    (by simp [reservedLocals, resolve, CBody.bind])
    (by simpa [reservedLocals, CBody.bind] using scope.instanceFresh)
    (by simpa [reservedLocals, resolve, CBody.bind] using scope.environmentBound)
    (by simpa [reservedLocals, resolve, CBody.bind] using scope.loggerBound)
    (by simpa [reservedLocals, resolve, CBody.bind] using scope.loggingBound)
    (by simpa [reservedLocals, CBody.bind] using scope.dstFresh)
    (by simpa [reservedLocals, CBody.bind] using scope.expectedFresh)
    (by simpa [reservedLocals, CBody.bind] using scope.counterFresh)
    pointer float bindings.size handle reserved.2
  refine ⟨reserved.1, ⟨TensorInstanceInit.initialized after (base.index slot.val) slot.val kind environment
    logger logging shape bounded', owned, SlotOwners.reserved_owner reserved.1⟩, ?_⟩
  exact successful program tag shape kind env types before after base ⟨block, [], 0⟩ capacity environment
    logger logging scope storage bindings.boolean bindings.atomicPointer bindings.size bindings.constantSize
    pointer float handle bindings.namedHelper bindings.namedAtomic bindings.atomicBound bindings.defined bounded
    volumeBounded outcome slot.isLt

/-- Release gets its live-owner and metadata premises from the creation
postcondition. Mirrors `StaticFactory.Created.release`, reusing the shared
model-agnostic release function. -/
theorem Created.release {after : Heap} {base : Address} {block : Nat} {owners : SlotOwners.State capacity}
    {slot : Fin capacity} {owner : Nat} {kind : Kind} {environment logger : Option Address} {logging : Bool}
    {shape : Tensor.Shape}
    (created : Created after base block owners slot owner kind environment logger logging shape)
    (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (bindings : StaticRelease.Bindings program tag)
    (flagsBound : interface.constants "rumoca_instance_flags" = some (.pointer (some ⟨block, [], 0⟩))) :
    let live := TensorInstanceInit.finalHeap after (base.index slot.val) slot.val kind environment logger
      logging shape
    let freed := replace live (AtomicSlots.address block slot) (CAtomicBoolean.cell false)
    SlotOwners.release owners slot owner = some (SlotOwners.update owners slot none) ∧
      SlotOwners.Represents block freed (SlotOwners.update owners slot none) ∧
      CStorage.Preserves live freed ∧
      (∀ query, query ≠ AtomicSlots.address block slot → freed query = live query) ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling StaticRelease.function.signature.name [.pointer (some (base.index slot.val))] live .done) behavior ↔
      behavior = .terminates [tag (.write (AtomicSlots.address block slot) false)] ⟨.void, freed⟩ :=
  StaticRelease.release_owned program tag _ base block owners slot owner bindings flagsBound
    created.represented created.owned created.initialized.slotValue

/-! ### The admission prefix and rejected admission

The tensor factory function reuses the model-agnostic scalar admission prefix
`FactoryPrefix.body`: the instance-name/token identity check (via the shared
`Identity.function` helper), the co-simulation capability guard, and the logging
capture. The prefix is parameterized over the model only through its instantiation
`token`; the reservation suffix is `TensorFactory.code`. Every admission proof is a
direct instance of the shared `FactoryValidation` lemmas with `creation` set to the
tensor reservation body, so no identity-validation proof is duplicated. -/
section
open FactoryArguments

/-- The tensor public factory function: the shared admission prefix followed by the
tensor reservation suffix. Parameterized over the model for its token only. -/
def function (model : Solve.FMI3Model source) (shape : Tensor.Shape) (kind : Kind)
    (tok : String := token model) : Function :=
  ⟨signature kind, FactoryPrefix.body model kind (code shape kind) tok, false⟩

/-- An accepted admission reduces the public call to the tensor reservation body.
Reuses `FactoryValidation.admission_equivalence` with the tensor reservation suffix. -/
theorem admission_accepts (program : CCalls.Events.Program E) (bindings : Identity.Bindings program)
    (model : Solve.FMI3Model source) (tok : String := token model) (shape : Tensor.Shape) (kind : Kind) (args : Raw) (heap : Heap)
    (stack : CCalls.Typed.Continuation) (name suppliedToken expected whitespace : Address)
    (nameBytes tokenBytes expectedBytes whitespaceBytes : List UInt8)
    (defined : program.internal.definitions (signature kind).name = some (.tree (function model shape kind tok)))
    (helper : program.internal.definitions Identity.function.signature.name = some (.tree Identity.function))
    (typeBindings : FactoryArguments.Types)
    (named : interface.constants Identity.function.signature.name = none)
    (supported : kind = .me ∨ FactoryEntry.unsupported args = false)
    (nameBound : args.name = some name) (tokenBound : args.token = some suppliedToken)
    (expectedBound : interface.literals tok = some expected)
    (whitespaceBound : interface.literals " \t\n\r\u000c\u000b" = some whitespace)
    (nameStored : CStringMemory.Contents heap name nameBytes)
    (tokenStored : CStringMemory.Contents heap suppliedToken tokenBytes)
    (expectedStored : CStringMemory.Contents heap expected expectedBytes)
    (whitespaceStored : CStringMemory.Contents heap whitespace whitespaceBytes)
    (fits : nameBytes.length < 2 ^ 64) :
    ∃ types, ∀ behavior,
      (CCalls.Events.machine program).Behaves
        (.calling (signature kind).name (arguments kind args) heap stack) behavior ↔
      (CCalls.Events.machine program).Behaves
        (.body (.running (FactoryValidation.remaining (code shape kind)
          (Identity.accepted nameBytes whitespaceBytes tokenBytes expectedBytes))
          (FactoryValidation.locals kind args
            (Identity.accepted nameBytes whitespaceBytes tokenBytes expectedBytes)) types heap)
          "fmi3Instance" stack) behavior :=
  FactoryValidation.admission_equivalence program bindings model tok kind (code shape kind) args heap stack
    name suppliedToken expected whitespace nameBytes tokenBytes expectedBytes whitespaceBytes defined helper
    typeBindings named supported nameBound tokenBound expectedBound whitespaceBound nameStored tokenStored
    expectedStored whitespaceStored fits

/-- A rejected admission (bad name or token) returns null with no reservation when
logging is disabled or absent. Reuses `FactoryValidation.rejected_silent`. -/
theorem rejected_silent (program : CCalls.Events.Program E) (bindings : Identity.Bindings program)
    (model : Solve.FMI3Model source) (tok : String := token model) (shape : Tensor.Shape) (kind : Kind) (args : Raw) (heap : Heap)
    (name suppliedToken expected whitespace : Address)
    (nameBytes tokenBytes expectedBytes whitespaceBytes : List UInt8)
    (defined : program.internal.definitions (signature kind).name = some (.tree (function model shape kind tok)))
    (helper : program.internal.definitions Identity.function.signature.name = some (.tree Identity.function))
    (typeBindings : FactoryArguments.Types)
    (named : interface.constants Identity.function.signature.name = none)
    (nullConstant : interface.constants "NULL" = some (.pointer none))
    (supported : kind = .me ∨ FactoryEntry.unsupported args = false)
    (nameBound : args.name = some name) (tokenBound : args.token = some suppliedToken)
    (expectedBound : interface.literals tok = some expected)
    (whitespaceBound : interface.literals " \t\n\r\u000c\u000b" = some whitespace)
    (nameStored : CStringMemory.Contents heap name nameBytes)
    (tokenStored : CStringMemory.Contents heap suppliedToken tokenBytes)
    (expectedStored : CStringMemory.Contents heap expected expectedBytes)
    (whitespaceStored : CStringMemory.Contents heap whitespace whitespaceBytes)
    (fits : nameBytes.length < 2 ^ 64)
    (rejected : Identity.accepted nameBytes whitespaceBytes tokenBytes expectedBytes = false)
    (quiet : (args.logger.isSome && args.logging) = false) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling (signature kind).name (arguments kind args) heap .done) behavior ↔
      behavior = .terminates [] ⟨.pointer none, heap⟩ :=
  FactoryValidation.rejected_silent program bindings model tok kind (code shape kind) args heap
    name suppliedToken expected whitespace nameBytes tokenBytes expectedBytes whitespaceBytes defined helper
    typeBindings named nullConstant supported nameBound tokenBound expectedBound whitespaceBound nameStored
    tokenStored expectedStored whitespaceStored fits rejected quiet behavior

end

/-! ### Creation followed by release restores the pool -/

/-- A creation followed by release of the same handle restores the original slot
ownership and links both executions in one program and atomic interface. Storage
and release-frame facts are supplied separately by `Created.release`. Mirrors
`StaticFactory.create_release`. -/
theorem create_release (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (shape : Tensor.Shape) (kind : Kind) (env : Locals) (types : CLoops.Types) (before after : Heap)
    (base : Address) (block capacity : Nat) (environment logger : Option Address) (logging : Bool)
    (scope : Scope env base ⟨block, [], 0⟩ capacity environment logger logging)
    (storage : ∀ slot : Fin capacity, TensorInstanceInit.Storage before (base.index slot.val) shape)
    (bindings : ReservationBindings program tag)
    (pointer : interface.types "Instance *" = some .pointer)
    (float : interface.types "fmi3Float64 *" = some .pointer)
    (handle : interface.types "fmi3Instance" = some .pointer)
    (releaseBindings : StaticRelease.Bindings program tag)
    (flagsBound : interface.constants "rumoca_instance_flags" = some (.pointer (some ⟨block, [], 0⟩)))
    (bounded : capacity < 2 ^ 64) (volumeBounded : shape.volume < 2 ^ 64)
    (owners : SlotOwners.State capacity) (represented : SlotOwners.Represents block before owners)
    (owner : Nat) (slot : Fin capacity)
    (outcome : CAtomicScan.Outcome ⟨block, [], 0⟩ capacity 0 before trace slot.val after) :
    ∃ live freed,
      Created after base block (SlotOwners.update owners slot (some owner)) slot owner kind
        environment logger logging shape ∧
      SlotOwners.Represents block freed owners ∧
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.body (.running (code shape kind) env types before) "fmi3Instance" .done) behavior ↔
        behavior = .terminates (trace.map tag) ⟨.pointer (some (base.index slot.val)), live⟩) ∧
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling StaticRelease.function.signature.name [.pointer (some (base.index slot.val))] live .done) behavior ↔
        behavior = .terminates [tag (.write (AtomicSlots.address block slot) false)] ⟨.void, freed⟩) := by
  obtain ⟨reserved, created, createdCall⟩ := successful_owned program tag shape kind env types before after
    base block capacity environment logger logging scope storage bindings pointer float handle bounded
    volumeBounded owners represented owner slot outcome
  obtain ⟨released, ownedAfter, _, _, releaseCall⟩ := created.release program tag releaseBindings flagsBound
  have vacant := (SlotOwners.reserve_iff.mp reserved).1
  have restored : SlotOwners.update (SlotOwners.update owners slot (some owner)) slot none = owners := by
    funext other
    by_cases same : other = slot
    · subst other; simp [SlotOwners.update, vacant]
    · simp [SlotOwners.update, same]
  rw [restored] at ownedAfter
  exact ⟨_, _, created, ownedAfter, createdCall, releaseCall⟩

/-! ### The tensor creation function contract -/

/-- The tensor instance-creation contract, mirroring the creation portion of
`StaticRuntime.FunctionContract` and the admission/rejection portion of
`FactoryAdmission.FunctionContract`. It bundles: an accepted admission reducing to
the reservation body; a rejected admission (bad name/token) returning null with no
reservation; successful creation returning an initialized handle; and exhaustion
returning null with no record change. Ownership and the create-then-release round
trip are separate theorems, not fields of this contract. -/
structure FunctionContract (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (model : Solve.FMI3Model source) (tok : String := token model) (shape : Tensor.Shape) : Prop where
  accepts : ∀ (bindings : Identity.Bindings program) (kind : Kind) (args : FactoryArguments.Raw)
    (heap : Heap) (stack : CCalls.Typed.Continuation) (name suppliedToken expected whitespace : Address)
    (nameBytes tokenBytes expectedBytes whitespaceBytes : List UInt8),
    program.internal.definitions (FactoryArguments.signature kind).name = some (.tree (function model shape kind tok)) →
    program.internal.definitions Identity.function.signature.name = some (.tree Identity.function) →
    FactoryArguments.Types → interface.constants Identity.function.signature.name = none →
    (kind = .me ∨ FactoryEntry.unsupported args = false) →
    args.name = some name → args.token = some suppliedToken →
    interface.literals tok = some expected →
    interface.literals " \t\n\r\u000c\u000b" = some whitespace →
    CStringMemory.Contents heap name nameBytes → CStringMemory.Contents heap suppliedToken tokenBytes →
    CStringMemory.Contents heap expected expectedBytes → CStringMemory.Contents heap whitespace whitespaceBytes →
    nameBytes.length < 2 ^ 64 →
    ∃ types, ∀ behavior,
      (CCalls.Events.machine program).Behaves
        (.calling (FactoryArguments.signature kind).name (FactoryArguments.arguments kind args) heap stack) behavior ↔
      (CCalls.Events.machine program).Behaves
        (.body (.running (FactoryValidation.remaining (code shape kind)
          (Identity.accepted nameBytes whitespaceBytes tokenBytes expectedBytes))
          (FactoryValidation.locals kind args
            (Identity.accepted nameBytes whitespaceBytes tokenBytes expectedBytes)) types heap)
          "fmi3Instance" stack) behavior
  created : ∀ (env : Locals) (types : CLoops.Types) (before after : Heap) (base flags : Address)
    (capacity : Nat) (environment logger : Option Address) (logging : Bool) (kind : Kind)
    (trace : List CAtomicBoolean.Calls.Event) (slot : Nat),
    Scope env base flags capacity environment logger logging →
    (∀ s : Fin capacity, TensorInstanceInit.Storage before (base.index s.val) shape) →
    (boolean : interface.types "_Bool" = some .boolean) →
    interface.types "volatile atomic_bool *" = some .pointer →
    interface.types "size_t" = some .size → interface.types "const size_t" = some .size →
    interface.types "Instance *" = some .pointer → interface.types "fmi3Float64 *" = some .pointer →
    interface.types "fmi3Instance" = some .pointer →
    interface.constants CAtomicScan.function.signature.name = none →
    interface.constants "atomic_exchange" = none →
    program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag boolean) →
    program.internal.definitions CAtomicScan.function.signature.name = some (.tree CAtomicScan.function) →
    capacity < 2 ^ 64 → shape.volume < 2 ^ 64 →
    CAtomicScan.Outcome flags capacity 0 before trace slot after → slot < capacity →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.body (.running (code shape kind) env types before) "fmi3Instance" .done) behavior ↔
      behavior = .terminates (trace.map tag) ⟨.pointer (some (base.index slot)),
        TensorInstanceInit.finalHeap after (base.index slot) slot kind environment logger logging shape⟩
  exhausted : ∀ (env : Locals) (types : CLoops.Types) (before after : Heap) (base flags : Address)
    (capacity : Nat) (environment logger : Option Address) (logging : Bool) (kind : Kind)
    (trace : List CAtomicBoolean.Calls.Event),
    Scope env base flags capacity environment logger logging →
    ReservationBindings program tag → capacity < 2 ^ 64 →
    CAtomicScan.Outcome flags capacity 0 before trace capacity after →
    interface.types "fmi3Instance" = some .pointer → resolve env "NULL" = some (.pointer none) →
    (logger.isSome && logging) = false →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.body (.running (code shape kind) env types before) "fmi3Instance" .done) behavior ↔
      behavior = .terminates (trace.map tag) ⟨.pointer none, before⟩
  rejected : ∀ (bindings : Identity.Bindings program) (kind : Kind) (args : FactoryArguments.Raw)
    (heap : Heap) (name suppliedToken expected whitespace : Address)
    (nameBytes tokenBytes expectedBytes whitespaceBytes : List UInt8),
    program.internal.definitions (FactoryArguments.signature kind).name = some (.tree (function model shape kind tok)) →
    program.internal.definitions Identity.function.signature.name = some (.tree Identity.function) →
    FactoryArguments.Types → interface.constants Identity.function.signature.name = none →
    interface.constants "NULL" = some (.pointer none) →
    (kind = .me ∨ FactoryEntry.unsupported args = false) →
    args.name = some name → args.token = some suppliedToken →
    interface.literals tok = some expected →
    interface.literals " \t\n\r\u000c\u000b" = some whitespace →
    CStringMemory.Contents heap name nameBytes → CStringMemory.Contents heap suppliedToken tokenBytes →
    CStringMemory.Contents heap expected expectedBytes → CStringMemory.Contents heap whitespace whitespaceBytes →
    nameBytes.length < 2 ^ 64 →
    Identity.accepted nameBytes whitespaceBytes tokenBytes expectedBytes = false →
    (args.logger.isSome && args.logging) = false →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (FactoryArguments.signature kind).name (FactoryArguments.arguments kind args) heap .done) behavior ↔
      behavior = .terminates [] ⟨.pointer none, heap⟩

/-- The tensor creation contract holds for the tensor factory function. -/
theorem contract (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (model : Solve.FMI3Model source) (tok : String := token model) (shape : Tensor.Shape) :
    FunctionContract program tag model tok shape where
  accepts bindings kind args heap stack name suppliedToken expected whitespace
      nameBytes tokenBytes expectedBytes whitespaceBytes defined helper typeBindings named supported
      nameBound tokenBound expectedBound whitespaceBound nameStored tokenStored expectedStored
      whitespaceStored fits :=
    admission_accepts program bindings model tok shape kind args heap stack name suppliedToken expected whitespace
      nameBytes tokenBytes expectedBytes whitespaceBytes defined helper typeBindings named supported
      nameBound tokenBound expectedBound whitespaceBound nameStored tokenStored expectedStored whitespaceStored fits
  created env types before after base flags capacity environment logger logging kind trace slot scope storage
      boolean atomicPointer size constantSize pointer float handle namedHelper namedAtomic atomicBound defined
      bounded volumeBounded outcome inside :=
    successful program tag shape kind env types before after base flags capacity environment logger logging
      scope storage boolean atomicPointer size constantSize pointer float handle namedHelper namedAtomic
      atomicBound defined bounded volumeBounded outcome inside
  exhausted env types before after base flags capacity environment logger logging kind trace scope bindings
      bounded outcome handle nullBound quiet :=
    exhausted_silent program tag shape kind env types before after base flags capacity environment logger
      logging scope bindings bounded outcome handle nullBound quiet
  rejected bindings kind args heap name suppliedToken expected whitespace nameBytes tokenBytes expectedBytes
      whitespaceBytes defined helper typeBindings named nullConstant supported nameBound tokenBound expectedBound
      whitespaceBound nameStored tokenStored expectedStored whitespaceStored fits rejectedId quiet :=
    rejected_silent program bindings model tok shape kind args heap name suppliedToken expected whitespace
      nameBytes tokenBytes expectedBytes whitespaceBytes defined helper typeBindings named nullConstant
      supported nameBound tokenBound expectedBound whitespaceBound nameStored tokenStored expectedStored
      whitespaceStored fits rejectedId quiet

end Rumoca.FMI3.TensorFactory
