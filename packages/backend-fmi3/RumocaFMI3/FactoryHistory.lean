import RumocaFMI3.FactoryControlStep

namespace Rumoca.FMI3.FactoryControl
open CTree CMemory CCalls CCalls.Events CCallSites RuntimeLinkage

/-- The host supplies the represented ME/CS ABI arguments at public entry.
This restricts the input call, not any later helper state or atomic outcome. -/
def AdmitsFactories (policy : Host.Policy) : Prop :=
  ∀ state thread name args, policy.admit state thread name args → ReservationOrigin.factory name →
    ∃ kind raw, name = (FactoryArguments.signature kind).name ∧ args = FactoryArguments.arguments kind raw

def RootReady (model : Solve.FMI3Model source) (objects : StaticFactory.Objects)
    (call : Host.Recording.Invocation) (state : Typed.State) : Prop :=
  ReservationOrigin.factory call.name → ∃ kind raw,
    call.name = (FactoryArguments.signature kind).name ∧ call.args = FactoryArguments.arguments kind raw ∧
    Control model kind raw objects state

theorem root_heap (ready : RootReady model objects call state) (heap : Heap) :
    RootReady model objects call (Concurrent.withHeap state heap) := by
  intro factory
  obtain ⟨kind, raw, name, args, control⟩ := ready factory
  exact ⟨kind, raw, name, args, control.withHeap heap⟩

variable {E : Type}

/-- Public invocation recording transports the complete factory control
invariant through every real host step. Other calls, completions and admitted
host heap changes are included, rather than silently dropped from the trace. -/
theorem recorded_controls (header : CFenv.Header) (objects : StaticFactory.Objects)
    (literals : CLiteralAddresses) :
    letI : CInterface := header.interface (StaticFactory.executionInterface objects literals)
    ∀ (model : Solve.FMI3Model source) (sigs : List Signature) (program : Events.Program E),
      program.internal = LiteralPreparation.program model sigs →
      (∀ name, ReservationOrigin.allowed name = false → NamedOnly program name) →
      (∀ kind, program.internal.definitions (FactoryArguments.signature kind).name =
        some (.tree (StaticFactory.function model kind))) →
      ∀ (expected whitespace : Address), literals (token model) = some expected →
      literals " \t\n\r\u000c\u000b" = some whitespace →
      ∀ tag : CAtomicBoolean.Calls.Event → E,
      program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag rfl) →
      ∀ policy, AdmitsFactories policy → ∀ heap ticks after,
      Transition.Events.Reaches (Host.Recording.Step program policy)
        ⟨⟨heap, fun _ => none⟩, Host.Recording.initial⟩ ticks after →
      Host.Recording.Controls (RootReady model objects) after := by
  letI : CInterface := header.interface (StaticFactory.executionInterface objects literals)
  intro model sigs program actual onlyNamed defined expected whitespace expectedBound whitespaceBound tag exchange
    policy admitted heap ticks after path
  have entry : ∀ serial state thread name args, policy.admit state thread name args →
      RootReady model objects ⟨serial, name, args⟩ (.calling name args state.heap .done) := by
    intro serial state thread name args accepted factory
    obtain ⟨kind, raw, rfl, rfl⟩ := admitted state thread name args accepted factory
    exact ⟨kind, raw, rfl, rfl, .entry state.heap⟩
  have preserves : ∀ call before events after, RootReady model objects call before →
      Events.Step program before events after → RootReady model objects call after := by
    intro call before events after ready step factory
    obtain ⟨kind, raw, name, args, control⟩ := ready factory
    exact ⟨kind, raw, name, args, control_step header objects literals model kind raw sigs program actual onlyNamed
      (defined kind) expected whitespace expectedBound whitespaceBound tag exchange before events after control step⟩
  exact Host.Recording.history_controls program policy (RootReady model objects)
    (fun _ _ ready heap => root_heap ready heap) entry preserves
    (by intro thread saved call selected active; contradiction) path

/-- From a raw public host history, every actual reservation exchange has
the original factory's recorded arguments, actual prepared scan continuation
and bounded array index. No separate helper-entry interval is a premise. -/
theorem logged_host_atomic (header : CFenv.Header) (objects : StaticFactory.Objects)
    (literals : CLiteralAddresses) :
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
        AdmitsFactories policy → ∀ heap trace current,
        Host.History program policy ⟨heap, fun _ => none⟩ trace current →
        ∃ ledger ticks, Host.Recording.erase ticks = trace ∧
          Transition.Events.Reaches (Host.Recording.Step program policy)
            ⟨⟨heap, fun _ => none⟩, Host.Recording.initial⟩ ticks ⟨current, ledger⟩ ∧
          (Host.Recording.issued ticks).Nodup ∧
          ∀ tracked values savedHeap stack,
            current.threads tracked = some (.calling "atomic_exchange" values savedHeap stack) →
            ∃ call kind raw types, ledger.active tracked = some call ∧
              call.name = (FactoryArguments.signature kind).name ∧ call.args = FactoryArguments.arguments kind raw ∧
              call.serial < ledger.next ∧ (∃ tick ∈ ticks, Host.Recording.Started tracked call tick) ∧
              CAtomicScan.ConcurrentInvariant.FullReady objects.flags objects.capacity
                (scanCaller model kind raw types) (.calling "atomic_exchange" values savedHeap stack) ∧
              ∃ k : Nat, k < objects.capacity ∧
                values = [.pointer (some (objects.flags.index k)), CAtomicBoolean.value true] := by
  letI : CInterface := header.interface (StaticFactory.executionInterface objects literals)
  intro model sigs covered defined expected whitespace expectedBound whitespaceBound tag observed range logger effect
    program domain memory policy admitted heap trace current path
  obtain ⟨ledger, ticks, erased, recorded, unique, origins⟩ :=
    ReservationOrigin.logged_host_origins model sigs covered tag rfl rfl rfl rfl observed range logger effect
      domain memory heap trace current path
  obtain ⟨_, _, _, _, library, _, _⟩ := logged_contract model sigs covered tag rfl rfl rfl rfl
    observed range logger none effect
  have controls := recorded_controls header objects literals model sigs program rfl
    (fun _ outside => ReservationOrigin.logged_named_only model sigs covered tag rfl rfl rfl rfl
      observed range logger effect outside) defined expected whitespace expectedBound whitespaceBound tag
    (library "atomic_exchange" _ rfl)
    policy admitted heap ticks ⟨current, ledger⟩ recorded
  refine ⟨ledger, ticks, erased, recorded, unique, ?_⟩
  intro tracked values savedHeap stack calling
  obtain ⟨call, active, factory, fresh, started⟩ :=
    origins tracked "atomic_exchange" values savedHeap stack calling (by decide +kernel)
  obtain ⟨kind, raw, name, args, control⟩ := controls tracked _ call calling active factory
  obtain ⟨types, scan, bounds⟩ := control.atomic_origin rfl
  exact ⟨call, kind, raw, types, active, name, args, fresh, started, scan, bounds⟩

end Rumoca.FMI3.FactoryControl
