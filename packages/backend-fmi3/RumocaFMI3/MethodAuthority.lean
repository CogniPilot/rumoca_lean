import RumocaFMI3.InstanceAuthority
import RumocaFMI3.InstanceCallProfile
import RumocaC.InvocationIdentity

namespace Rumoca.FMI3.InstanceAuthority
open CTree CMemory CCalls
variable {capacity : Nat}

/-- A borrowed resource retains the real public method, exact first argument,
and original invocation serial. Other arguments retain their per-API domains. -/
def Borrowing (state : State capacity) (ledger : Host.Recording.Ledger)
    (thread : Nat) (handle : Handle capacity) (instances : Nat) : Prop :=
  ∃ call api tail, ledger.active thread = some call ∧ PublicAPI.Entry.ordinary api = true ∧
    call.name = api.signature.name ∧ call.args = handle.value instances :: tail ∧
    state handle.slot = some ⟨handle.lease, .using call.serial⟩

def Phase.ticket : Phase → Option Nat
  | .client => none
  | .using call | .releasing call => some call

/-- The argument-origin component of the future legal caller invariant.
Other components must classify each phase's API, establish value/buffer frames
and retain publication; this relation alone is not a legal-history predicate. -/
def ArgumentOrigins (state : State capacity) (ledger : Host.Recording.Ledger) (instances : Nat) : Prop :=
  ∀ slot account serial, state slot = some account → account.phase.ticket = some serial →
    ∃ thread call tail, ledger.active thread = some call ∧ call.serial = serial ∧
      call.args = .pointer (some (AtomicSlots.address instances slot)) :: tail

/-- A real invocation cannot borrow resources for two distinct instance slots:
its recorded first argument and serial uniquely determine that slot. -/
theorem ticket_unique (origins : ArgumentOrigins state ledger instances)
    (unique : Host.Recording.Unique ledger)
    (first : state left = some firstAccount) (second : state right = some secondAccount)
    (firstTicket : firstAccount.phase.ticket = some serial)
    (secondTicket : secondAccount.phase.ticket = some serial) : left = right := by
  obtain ⟨firstThread, firstCall, firstTail, firstActive, firstSerial, firstArgs⟩ :=
    origins left firstAccount serial first firstTicket
  obtain ⟨secondThread, secondCall, secondTail, secondActive, secondSerial, secondArgs⟩ :=
    origins right secondAccount serial second secondTicket
  have same := (unique firstThread firstCall secondThread secondCall firstActive secondActive
    (firstSerial.trans secondSerial.symm)).2
  cases same
  have heads := congrArg List.head? (firstArgs.symm.trans secondArgs)
  have addresses : AtomicSlots.address instances left = AtomicSlots.address instances right := by simpa using heads
  exact AtomicSlots.address_injective instances addresses

/-- Returning the current method's resource cannot restore any other slot,
including a resource borrowed by another invocation or a reused generation. -/
theorem complete_frame {handle : Handle capacity}
    (origins : ArgumentOrigins state ledger instances) (unique : Host.Recording.Unique ledger)
    (borrowed : state handle.slot = some ⟨handle.lease, .using invocation⟩)
    (different : slot ≠ handle.slot) : completeUse state invocation slot = state slot := by
  cases found : state slot with
  | none => simp [completeUse, found]
  | some account =>
    rcases account with ⟨lease, phase⟩
    cases phase with
    | client => simp [completeUse, found]
    | releasing call => simp [completeUse, found]
    | «using» call =>
      by_cases same : call = invocation
      · subst call
        exact False.elim (different (ticket_unique origins unique found borrowed rfl rfl))
      · simp [completeUse, found, same]

/-- Ordinary completion never creates or revokes a physical publication,
even before using its independent return-type execution theorem. -/
theorem method_observation {api : PublicAPI.Entry} (active : ledger.active thread = some call)
    (ordinary : api.ordinary = true) (named : call.name = api.signature.name) :
    PublicationRegistry.observe published instances ledger thread value = published := by
  have notFactory : ¬ ReservationOrigin.factory call.name := by
    rw [named]
    exact (PublicAPI.ordinary_signature api ordinary).2.2.2
  cases value with
  | pointer address => cases address <;> simp [PublicationRegistry.observe, active, notFactory]
  | integer | float64 | void => rfl

variable [interface : CInterface] {E : Type}

/-- Real ordinary-method entry borrows the provided live handle under the
recorded fresh serial. Signature classification comes from the emitted API
index, not a caller-supplied mode switch on an arbitrary function name. -/
theorem method_enter (program : Events.Program E) (policy : Host.Policy)
    (before : PublicationRegistry.Configuration capacity) (authority : State capacity)
    (instances flags thread : Nat) (handle : Handle capacity) (api : PublicAPI.Entry) (tail : List Value)
    (ordinary : api.ordinary = true) (linked : Linked authority before.publications)
    (owned : Owns authority handle)
    (actual : Host.Step program policy before.recorded.runtime thread
      (.invoke api.signature.name (handle.value instances :: tail)) after) :
    let action := Host.Action.invoke (E := E) api.signature.name (handle.value instances :: tail)
    let ledger := Host.Recording.advance before.recorded.ledger thread action
    ∃ following,
      enter authority handle before.recorded.ledger.next .use = some following ∧
      Borrowing following ledger thread handle instances ∧ Linked following before.publications ∧
      PublicationRegistry.Step program policy instances flags before
        [Host.Recording.stamp before.recorded.ledger thread action]
        ⟨⟨after, ledger⟩, before.publications⟩ := by
  dsimp only
  let following := Function.update authority handle.slot (some ⟨handle.lease, .using before.recorded.ledger.next⟩)
  have entered : enter authority handle before.recorded.ledger.next .use = some following :=
    enter_iff.mpr ⟨owned, rfl⟩
  refine ⟨following, entered, ?_, enter_linked linked entered, .record actual⟩
  refine ⟨⟨before.recorded.ledger.next, api.signature.name, handle.value instances :: tail⟩,
    api, tail, ?_, ordinary, rfl, rfl, ?_⟩
  · simp [Host.Recording.advance, Host.Recording.bind]
  · simp [following]

/-- The actual observed completion returns precisely its own borrowed
resource and leaves all other slots alone. It uses the same C/host completion
and computed publication step, rather than a replacement execution rule. -/
theorem method_complete (program : Events.Program E) (policy : Host.Policy)
    (before : PublicationRegistry.Configuration capacity) (authority : State capacity)
    (instances flags thread : Nat) (handle : Handle capacity)
    (linked : Linked authority before.publications)
    (borrowing : Borrowing authority before.recorded.ledger thread handle instances)
    (origins : ArgumentOrigins authority before.recorded.ledger instances)
    (unique : Host.Recording.Unique before.recorded.ledger)
    (actual : Host.Step program policy before.recorded.runtime thread (.complete value) after) :
    ∃ call, before.recorded.ledger.active thread = some call ∧
      Owns (completeUse authority call.serial) handle ∧
      Linked (completeUse authority call.serial) before.publications ∧
      (∀ slot, slot ≠ handle.slot → completeUse authority call.serial slot = authority slot) ∧
      after.heap = before.recorded.runtime.heap ∧
      PublicationRegistry.Step program policy instances flags before
        [Host.Recording.stamp before.recorded.ledger thread (.complete value)]
        ⟨⟨after, Host.Recording.advance (E := E) before.recorded.ledger thread (.complete value)⟩, before.publications⟩ := by
  obtain ⟨call, api, tail, active, ordinary, named, _, borrowed⟩ := borrowing
  refine ⟨call, active, complete_owned borrowed, complete_linked linked,
    fun slot different => complete_frame origins unique borrowed different, ?_, ?_⟩
  · rw [(Host.complete_iff.mp actual).2]
  · have unchanged := method_observation (published := before.publications) (instances := instances)
      (value := value) active ordinary named
    simpa only [PublicationRegistry.advance, unchanged] using
      (PublicationRegistry.Step.record (ledger := before.recorded.ledger) (publications := before.publications) (instances := instances) (flags := flags) actual)

end Rumoca.FMI3.InstanceAuthority
