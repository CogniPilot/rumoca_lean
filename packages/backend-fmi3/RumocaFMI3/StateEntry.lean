import RumocaFMI3.GuardedCalls
import RumocaFMI3.ScalarAccess
import RumocaFMI3.StateCalls
import RumocaC.FiniteValue

noncomputable section
namespace Rumoca.FMI3.StateCalls.Entry
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses
open CTree CMemory CBody

def values (handle buffer : Option Address) (count : UInt64) : List Value :=
  [.pointer handle, .pointer buffer, .integer count.toNat]

def parameters (handle buffer : Option Address) (count : UInt64) : Locals :=
  CBody.bind (CBody.bind (CBody.bind (fun _ => none) "nContinuousStates" (.integer count.toNat))
    "continuousStates" (.pointer buffer)) "instance" (.pointer handle)

theorem parameters_bound (write : Bool) (handle buffer : Option Address) (count : UInt64) :
    CCalls.parameters (signature write).parameters (values handle buffer count) =
      some (parameters handle buffer count) := by
  have converted : CBody.cast "size_t" (.integer count.toNat) = some (.integer count.toNat) :=
    CLoops.Calls.cast_of_type "size_t" .size _ _ (by rfl) (CLoops.convert_size_nat _ count.toNat_lt_size)
  cases write <;> simp only [signature, values, CCalls.parameters,
    CCalls.parameterType, Bool.false_eq_true, ↓reduceIte, converted] <;> rfl

omit static in
theorem parameters_valid (p buffer : Address) :
    parameters (some p) (some buffer) 1 = StateProofs.parameters p buffer := by
  rfl

def command (write : Bool) : Command := if write then .setStates else .getStates

def action (write : Bool) : List Stmt :=
    if write then
      [Runtime.reject (Runtime.negate (Runtime.finite (.index (Runtime.v "continuousStates") (Runtime.n 0))))
        "State must be finite", .assign Runtime.x (.index (Runtime.v "continuousStates") (Runtime.n 0)), Runtime.ok]
    else [.assign (.index (Runtime.v "continuousStates") (Runtime.n 0)) Runtime.x, Runtime.ok]

def tail (write : Bool) : List Stmt :=
  Runtime.scalarAccessCheck "continuousStates" "nContinuousStates" ++ action write

omit static in
theorem body_eq (model : Solve.FMI3Model source) (write : Bool) :
    Runtime.body model (signature write) = Runtime.require (command write) ++ tail write := by
  cases write <;> rfl

theorem null_behaviors (model : Solve.FMI3Model source) (write : Bool) (program : CCalls.Events.Program E)
    (heap : Heap) (buffer : Option Address) (count : UInt64)
    (defined : program.internal.definitions (signature write).name =
      some (.tree (Runtime.function model (signature write)))) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling (signature write).name (values none buffer count) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  apply GuardedCalls.null_behaviors program (Runtime.function model (signature write))
    (Runtime.modeGuard (command write) :: tail write) (values none buffer count)
    (parameters none buffer count) heap defined (parameters_bound write none buffer count)
  · change Runtime.body model (signature write) = _
    rw [body_eq]
    simp only [Runtime.require, List.append_assoc, List.singleton_append]
  · cases write <;> rfl
  · exact BodyEmbedding.body_closed model _
  · simp [parameters, CBody.bind]
  · simp [parameters, CBody.bind]
  · simp [parameters, CBody.bind]

theorem rejected_all_behaviors (model : Solve.FMI3Model source) (write : Bool)
    (program : CCalls.Events.Program E) (heap : Heap)
    (p message category logger : Address) (environment buffer : Option Address) (count : UInt64)
    (kind : Kind) (mode : Mode) (name : String) (foreign : CCalls.Events.External E)
    (defined : program.internal.definitions (signature write).name =
      some (.tree (Runtime.function model (signature write))))
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (messageBound : static.addresses ErrorCalls.rejectionMessage = some message)
    (address : program.addresses logger = some name)
    (external : program.externals name = some foreign)
    (prototype : foreign.signature = Logging.signature name)
    (literal : static.addresses "logStatus" = some category)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (hl : load heap (p.member "logger") = some (.pointer (some logger)))
    (hg : load heap (p.member "logging") = some (.integer 1))
    (he : load heap (p.member "environment") = some (.pointer environment))
    (rejected : ¬ Reference.Allowed (command write) kind mode) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling (signature write).name (values (some p) buffer count) heap .done) behavior ↔
      (∃ events value after, foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) events value after ∧
        behavior = .terminates events ⟨.integer 3, after⟩) ∨
      ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) events value after) ∧ behavior = .wrong []) := by
  exact GuardedCalls.rejected_all_behaviors program (Runtime.function model (signature write))
    (command write) (tail write) (values (some p) buffer count) (parameters (some p) buffer count)
    heap p message category logger environment kind mode name foreign defined
    (parameters_bound write (some p) buffer count) (body_eq model write) (by cases write <;> rfl)
    (BodyEmbedding.body_closed model _) helper (by simp [parameters, CBody.bind])
    (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind])
    messageBound address external prototype literal hk hm hl hg he rejected behavior

theorem rejected_silent_behaviors (model : Solve.FMI3Model source) (write : Bool)
    (program : CCalls.Events.Program E) (heap : Heap) (p message : Address)
    (buffer logger : Option Address) (count : UInt64) (kind : Kind) (mode : Mode)
    (defined : program.internal.definitions (signature write).name =
      some (.tree (Runtime.function model (signature write))))
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (messageBound : static.addresses ErrorCalls.rejectionMessage = some message)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (hl : load heap (p.member "logger") = some (.pointer logger))
    (hg : load heap (p.member "logging") = some (.integer 0))
    (rejected : ¬ Reference.Allowed (command write) kind mode) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling (signature write).name (values (some p) buffer count) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩ := by
  exact GuardedCalls.rejected_silent_behaviors program (Runtime.function model (signature write))
    (command write) (tail write) (values (some p) buffer count) (parameters (some p) buffer count)
    heap p message logger kind mode defined (parameters_bound write (some p) buffer count)
    (body_eq model write) (by cases write <;> rfl) (BodyEmbedding.body_closed model _)
    helper (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind])
    (by simp [parameters, CBody.bind]) messageBound hk hm hl hg rejected behavior

end Rumoca.FMI3.StateCalls.Entry

namespace Rumoca.FMI3.StateCalls.Entry
variable [static : StaticLiterals]
private local instance validationInterface : CInterface := cInterface static.addresses
open CTree CMemory CBody

theorem invalid_run (model : Solve.FMI3Model source) (write : Bool)
    (heap : Heap) (p : Address) (buffer : Option Address) (count : UInt64) (kind : Kind) (mode : Mode)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed (command write) kind mode)
    (invalid : count.toNat ≠ 1 ∨ buffer = none) :
    run 4 (.running (Runtime.body model (signature write)) (parameters (some p) buffer count) heap) =
      some (.running (Runtime.fail "Expected one continuous state" :: action write)
        (CBody.bind (parameters (some p) buffer count) "m" (.pointer (some p))) heap) := by
  have accepted := LifecycleGuard.accept (parameters (some p) buffer count) heap p (command write)
    kind mode (tail write) (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind]) hk hm allowed
  rw [body_eq, show 4 = 3 + 1 from rfl, run_add, accepted]
  exact ScalarAccess.invalid_run _ heap "continuousStates" "nContinuousStates" buffer count (action write)
    (by simp [parameters, CBody.bind, resolve]) (by simp [parameters, CBody.bind, resolve]) invalid

theorem invalid_prefix (model : Solve.FMI3Model source) (write : Bool)
    (heap : Heap) (p : Address) (buffer : Option Address) (count : UInt64) (kind : Kind) (mode : Mode)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed (command write) kind mode)
    (invalid : count.toNat ≠ 1 ∨ buffer = none) :
    GuardedCalls.FailurePrefix (Runtime.function model (signature write)) (values (some p) buffer count)
      heap p "Expected one continuous state" heap := by
  refine ⟨by cases write <;> rfl, BodyEmbedding.body_closed model (signature write),
    parameters (some p) buffer count, CBody.bind (parameters (some p) buffer count) "m" (.pointer (some p)),
    action write, 4, parameters_bound write (some p) buffer count,
    invalid_run model write heap p buffer count kind mode hk hm allowed invalid, ?_, ?_⟩
  · simp [parameters, CBody.bind]
  · simp [CBody.bind, resolve]

theorem nonfinite_run (model : Solve.FMI3Model source) (heap : Heap) (p buffer : Address) (value : Value)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer 3))
    (input : load heap buffer = some value) (nonfinite : value.isFinite = some false) :
    run 5 (.running (Runtime.body model (signature true)) (parameters (some p) (some buffer) 1) heap) =
      some (.running (Runtime.fail "State must be finite" ::
        [.assign Runtime.x (.index (Runtime.v "continuousStates") (Runtime.n 0)), Runtime.ok])
        (CBody.bind (parameters (some p) (some buffer) 1) "m" (.pointer (some p))) heap) := by
  have accepted := LifecycleGuard.accept (parameters (some p) (some buffer) 1) heap p (command true)
    .me .continuous (tail true) (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind])
    hk hm (by simp [command, Reference.Allowed])
  rw [body_eq, show 5 = 3 + 2 from rfl, run_add, accepted]
  have checked := ScalarAccess.valid_run
    (CBody.bind (parameters (some p) (some buffer) 1) "m" (.pointer (some p))) heap
    "continuousStates" "nContinuousStates" buffer (action true)
    (by simp [parameters, CBody.bind, resolve]) (by simp [parameters, CBody.bind, resolve])
  simp only [Option.bind_some, tail]
  rw [show 2 = 1 + 1 from rfl, run_add, checked]
  simp [action, Runtime.reject, Runtime.branch, Runtime.negate, Runtime.finite, Runtime.call,
    Runtime.v, Runtime.n, run, next, eval, parameters, CBody.bind, resolve, constants,
    Value.address, boolean, Value.truth, input, nonfinite]

theorem nonfinite_prefix (model : Solve.FMI3Model source) (heap : Heap) (p buffer : Address) (value : Value)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer 3))
    (input : load heap buffer = some value) (nonfinite : value.isFinite = some false) :
    GuardedCalls.FailurePrefix (Runtime.function model (signature true)) (values (some p) (some buffer) 1)
      heap p "State must be finite" heap := by
  refine ⟨rfl, BodyEmbedding.body_closed model (signature true), parameters (some p) (some buffer) 1,
    CBody.bind (parameters (some p) (some buffer) 1) "m" (.pointer (some p)), _, 5,
    parameters_bound true (some p) (some buffer) 1, nonfinite_run model heap p buffer value hk hm input nonfinite,
    ?_, ?_⟩
  · simp [parameters, CBody.bind]
  · simp [CBody.bind, resolve]

end Rumoca.FMI3.StateCalls.Entry

namespace Rumoca.FMI3.StateCalls.Entry
open CTree CMemory

inductive FailureReason where
  | lifecycle | access | nonfinite
  deriving DecidableEq

def failureMessage : FailureReason → String
  | .lifecycle => ErrorCalls.rejectionMessage
  | .access => "Expected one continuous state"
  | .nonfinite => "State must be finite"

def FailureCondition (reason : FailureReason) (write : Bool) (kind : Kind) (mode : Mode)
    (heap : Heap) (buffer : Option Address) (count : UInt64) : Prop :=
  match reason with
  | .lifecycle => ¬ Reference.Allowed (command write) kind mode
  | .access => Reference.Allowed (command write) kind mode ∧ (count.toNat ≠ 1 ∨ buffer = none)
  | .nonfinite => write = true ∧ Reference.Allowed (command write) kind mode ∧ count = 1 ∧
      ∃ address bits, buffer = some address ∧ load heap address = some (.float64 bits) ∧
        (Value.float64 bits).isFinite = some false

/-- All state accessor arguments fall into a null, permitted success or
specific failure case. Readability is needed only when a permitted setter
with a valid count and pointer actually reaches its input load. -/
theorem query_cases (write : Bool) (kind : Kind) (mode : Mode) (heap : Heap)
    (handle buffer : Option Address) (count : UInt64)
    (readable : write = true → Reference.Allowed (command write) kind mode → count = 1 →
      ∀ address, buffer = some address → ∃ bits, load heap address = some (.float64 bits)) :
    handle = none ∨ ∃ p, handle = some p ∧
      ((∃ address, buffer = some address ∧ count = 1 ∧ Reference.Allowed (command write) kind mode ∧
        (write = false ∨ ∃ x : Binary64.Value, load heap address = some (.finite x))) ∨
       ∃ reason, FailureCondition reason write kind mode heap buffer count) := by
  classical
  cases handle with
  | none => exact Or.inl rfl
  | some p =>
      refine Or.inr ⟨p, rfl, ?_⟩
      by_cases allowed : Reference.Allowed (command write) kind mode
      · by_cases size : count.toNat = 1
        · have countOne : count = 1 := UInt64.toNat_inj.mp size
          cases buffer with
          | none => exact Or.inr ⟨.access, allowed, Or.inr rfl⟩
          | some address =>
              cases write with
              | false => exact Or.inl ⟨address, rfl, countOne, allowed, Or.inl rfl⟩
              | true =>
                  obtain ⟨bits, loaded⟩ := readable rfl allowed countOne address rfl
                  rcases Value.float64_cases bits with ⟨x, same⟩ | nonfinite
                  · exact Or.inl ⟨address, rfl, countOne, allowed, Or.inr ⟨x, same ▸ loaded⟩⟩
                  · exact Or.inr ⟨.nonfinite, rfl, allowed, countOne, address, bits, rfl, loaded, nonfinite⟩
        · exact Or.inr ⟨.access, allowed, Or.inl size⟩
      · exact Or.inr ⟨.lifecycle, allowed⟩

theorem failure_unique
    (first : FailureCondition a write kind mode heap buffer count)
    (second : FailureCondition b write kind mode heap buffer count) : a = b := by
  cases a <;> cases b <;> simp only [FailureCondition] at first second
  all_goals try rfl
  · exact False.elim (first second.1)
  · exact False.elim (first second.2.1)
  · exact False.elim (second first.1)
  · obtain ⟨_, _, rfl, address, bits, rfl, _, _⟩ := second
    rcases first.2 with wrongCount | missing
    · exact False.elim (wrongCount rfl)
    · cases missing
  · exact False.elim (second first.2.1)
  · obtain ⟨_, _, rfl, address, bits, rfl, _, _⟩ := first
    rcases second.2 with wrongCount | missing
    · exact False.elim (wrongCount rfl)
    · cases missing

end Rumoca.FMI3.StateCalls.Entry

namespace Rumoca.FMI3.StateCalls.Entry
variable [static : StaticLiterals]
private local instance completeInterface : CInterface := cInterface static.addresses
open CTree CMemory CBody

theorem failure_prefix (model : Solve.FMI3Model source) (write : Bool) (reason : FailureReason)
    (heap : Heap) (p : Address) (buffer : Option Address) (count : UInt64) (kind : Kind) (mode : Mode)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (condition : FailureCondition reason write kind mode heap buffer count) :
    GuardedCalls.FailurePrefix (Runtime.function model (signature write)) (values (some p) buffer count)
      heap p (failureMessage reason) heap := by
  cases reason with
  | lifecycle =>
      refine ⟨by cases write <;> rfl, BodyEmbedding.body_closed model (signature write),
        parameters (some p) buffer count, CBody.bind (parameters (some p) buffer count) "m" (.pointer (some p)),
        tail write, 3, parameters_bound write (some p) buffer count, ?_, ?_, ?_⟩
      · have executed := LifecycleGuard.reject_prefix (parameters (some p) buffer count) heap p
          (command write) kind mode (tail write) (by simp [parameters, CBody.bind])
          (by simp [parameters, CBody.bind]) hk hm condition
        rw [← body_eq model write] at executed
        exact executed
      · simp [parameters, CBody.bind]
      · simp [CBody.bind, resolve]
  | access => exact invalid_prefix model write heap p buffer count kind mode hk hm condition.1 condition.2
  | nonfinite =>
      obtain ⟨rfl, allowed, rfl, address, bits, rfl, loaded, invalid⟩ := condition
      change kind = .me ∧ mode = .continuous at allowed
      obtain ⟨rfl, rfl⟩ := allowed
      exact nonfinite_prefix model heap p address (.float64 bits) hk hm loaded invalid

end Rumoca.FMI3.StateCalls.Entry
