import RumocaFMI3.ReservationRegistryHistory
import RumocaFMI3.ClearCallPolicy
import RumocaFMI3.FactoryHistory

noncomputable section
namespace Rumoca.FMI3.ReservationRegistry
open CTree CMemory CCalls CCalls.Events RuntimeLinkage

/-- Instantiate the registry's control obligations with the actual generated
factory and clear-call proofs. The input is the entire recorded host prefix. -/
theorem logged_ready (header : CFenv.Header) (objects : StaticFactory.Objects)
    (literals : CLiteralAddresses) (block : Nat)
    (flags : objects.flags = ⟨block, [], 0⟩) :
    letI : CInterface := header.interface (StaticFactory.executionInterface objects literals)
    ∀ (model : Solve.FMI3Model source) (sigs : List Signature) (covered : PublicAPI.Covered sigs),
      (∀ kind, (LiteralPreparation.program model sigs).definitions (FactoryArguments.signature kind).name =
        some (.tree (StaticFactory.function model kind))) →
      ∀ (expected whitespace : Address), literals (token model) = some expected →
      literals " \t\n\r\u000c\u000b" = some whitespace →
      ∀ (tag : CAtomicBoolean.Calls.Event → Invocation)
        (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
        (logger : Address) (effect : ReturningEffect (Logging.signature hostName)),
      let program := logged model sigs covered tag rfl rfl rfl rfl observed range logger effect
      ∀ (domain : Concurrent.State → Nat → Signature → List Value → Prop)
        (memory : Concurrent.State → Nat → Heap → Prop),
        let policy := Host.publicPolicy sigs domain memory
        FactoryControl.AdmitsFactories policy → ∀ heap ticks current,
        Transition.Events.Reaches (Host.Recording.Step program policy)
          ⟨⟨heap, fun _ => none⟩, Host.Recording.initial⟩ ticks current →
        Ready block objects.capacity current := by
  letI : CInterface := header.interface (StaticFactory.executionInterface objects literals)
  intro model sigs covered defined expected whitespace expectedBound whitespaceBound tag observed range logger effect
    program domain memory policy admitted heap ticks current path
  obtain ⟨_, _, _, _, library, _, _⟩ := logged_contract model sigs covered tag rfl rfl rfl rfl
    observed range logger none effect
  have controls := FactoryControl.recorded_controls header objects literals model sigs program rfl
    (fun _ outside => ReservationOrigin.logged_named_only model sigs covered tag rfl rfl rfl rfl
      observed range logger effect outside) defined expected whitespace expectedBound whitespaceBound tag
    (library "atomic_exchange" _ rfl) policy admitted heap ticks current path
  have origins := ReservationOrigin.logged_controls model sigs covered tag rfl rfl rfl rfl
    observed range logger effect domain memory heap ticks current path
  have aligned := (Host.Recording.history_invariants path
    (Host.Recording.initial_aligned heap) Host.Recording.initial_fresh).1
  refine ⟨?_, ?_⟩
  · intro thread args savedHeap stack calling
    obtain ⟨call, active⟩ := Host.Recording.aligned_active aligned calling
    have factory := ReservationOrigin.root_excluded (origins thread _ call calling active)
      (show ReservationOrigin.allowed "atomic_exchange" = false by decide +kernel)
    obtain ⟨kind, raw, _, _, control⟩ := controls thread _ call calling active factory
    obtain ⟨_, _, k, inside, arguments⟩ := control.atomic_origin rfl
    refine ⟨⟨k, inside⟩, call, ?_, active⟩
    simpa [flags, Address.index, AtomicSlots.address] using arguments
  · exact ClearCallPolicy.logged_history model sigs covered tag rfl rfl rfl rfl
      observed range logger effect domain memory heap _ current.runtime
      (Host.Recording.history_erases path)

/-- Starting with the actual initially free atomic array, raw public host
history computes all invocation and reservation records and derives the final
flag representation. No current owner/flag representation or annotated atomic
history is an input. This establishes physical reservation, not live-handle
publication or release authority. -/
theorem logged_reservations (header : CFenv.Header) (objects : StaticFactory.Objects)
    (literals : CLiteralAddresses) (block : Nat)
    (flags : objects.flags = ⟨block, [], 0⟩) :
    letI : CInterface := header.interface (StaticFactory.executionInterface objects literals)
    ∀ (model : Solve.FMI3Model source) (sigs : List Signature) (covered : PublicAPI.Covered sigs),
      (∀ kind, (LiteralPreparation.program model sigs).definitions (FactoryArguments.signature kind).name =
        some (.tree (StaticFactory.function model kind))) →
      ∀ (expected whitespace : Address), literals (token model) = some expected →
      literals " \t\n\r\u000c\u000b" = some whitespace →
      ∀ (tag : CAtomicBoolean.Calls.Event → Invocation)
        (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
        (logger : Address) (effect : ReturningEffect (Logging.signature hostName)),
      (∀ args before result after, effect.execute args before result after → CAtomicBoolean.Preserves before after) →
      let program := logged model sigs covered tag rfl rfl rfl rfl observed range logger effect
      ∀ (domain : Concurrent.State → Nat → Signature → List Value → Prop)
        (memory : Concurrent.State → Nat → Heap → Prop),
        (∀ state thread heap, memory state thread heap → CAtomicBoolean.Preserves state.heap heap) →
        let policy := Host.publicPolicy sigs domain memory
        FactoryControl.AdmitsFactories policy → ∀ initialHeap trace current,
        let heap := CAtomicBoolean.initial initialHeap block objects.capacity
        Host.History program policy ⟨heap, fun _ => none⟩ trace current →
        ∃ ledger ticks, ∃ owners : SlotOwners.State objects.capacity,
          Host.Recording.erase ticks = trace ∧
          Transition.Events.Reaches (Host.Recording.Step program policy)
            ⟨⟨heap, fun _ => none⟩, Host.Recording.initial⟩ ticks ⟨current, ledger⟩ ∧
          (Host.Recording.issued ticks).Nodup ∧
          Transition.Events.Reaches (Step program policy block)
            ⟨⟨⟨heap, fun _ => none⟩, Host.Recording.initial⟩, fun _ => none⟩ ticks
            ⟨⟨current, ledger⟩, owners⟩ ∧
          SlotOwners.Represents block current.heap owners := by
  letI : CInterface := header.interface (StaticFactory.executionInterface objects literals)
  intro model sigs covered defined expected whitespace expectedBound whitespaceBound tag observed range logger effect callback
    program domain memory hostFrame policy admitted initialHeap trace current heap path
  obtain ⟨ledger, ticks, erased, recorded⟩ := Host.Recording.history_lift program policy path Host.Recording.initial
  obtain ⟨owners, registry⟩ := history_lift program policy block recorded (fun _ : Fin objects.capacity => none)
  obtain ⟨_, _, _, _, library, _, _⟩ := logged_contract model sigs covered tag rfl rfl rfl rfl
    observed range logger none effect
  refine ⟨ledger, ticks, owners, erased, recorded, Host.Recording.history_unique_ids recorded, registry, ?_⟩
  exact history_represents program policy tag rfl rfl (library "atomic_exchange" _ rfl) (library "atomic_store" _ rfl)
    (AtomicFlagFrame.logged_flags model sigs covered tag rfl rfl rfl rfl observed range logger effect callback)
    hostFrame _
    (logged_ready header objects literals block flags model sigs covered defined expected whitespace expectedBound whitespaceBound
      tag observed range logger effect domain memory admitted heap)
    (.refl _) registry (SlotOwners.initialized initialHeap block objects.capacity)

end Rumoca.FMI3.ReservationRegistry
