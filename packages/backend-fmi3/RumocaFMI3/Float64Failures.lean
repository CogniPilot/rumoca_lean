import RumocaFMI3.Float64Get
import RumocaFMI3.FailureSites

noncomputable section
namespace Rumoca.FMI3.Float64Calls
open CTree CMemory CBody CLoops
variable [static : StaticLiterals]
private local instance errorSiteInterface : CInterface := cInterface static.addresses

theorem get_array_error_site (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (p : Address) (references values : Option Address) (n m : UInt64)
    (kind : Kind) (mode : Mode)
    (defined : program.internal.definitions (signature false).name =
      some (.tree (Runtime.function model (signature false))))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode)
    (invalid : ¬ ArrayAccess.Valid references values n m) :
    GuardedCalls.FailureSite program
      (.calling (signature false).name (arguments (some p) references values n m) heap .done)
      heap p "Invalid Float64 array lengths or pointers" := by
  have guarded := get_guard_run model heap p references values n m kind mode hk hm allowed
  rw [if_neg invalid] at guarded
  obtain ⟨types, reached⟩ := CCalls.Events.body_prefix_reaches program (Runtime.function model (signature false))
    (arguments (some p) references values n m) (parameters (some p) references values n m)
    (locals p references values n m) heap heap
    (Runtime.fail "Invalid Float64 array lengths or pointers" :: afterGuard) .done 4
    defined (parameters_bound false _ _ _ _ _) (BodyEmbedding.body_closed model (signature false)) guarded
  refine ⟨locals p references values n m, types, afterGuard, reached, ?_, ?_⟩
  · simp [locals, parameters, CBody.bind]
  · simp [locals, CBody.bind, resolve]

theorem get_reference_error_site (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (p : Address) (pointer buffer : Option Address) (n : UInt64) (references : Nat → UInt32)
    (kind : Kind) (mode : Mode) (bad : Nat)
    (defined : program.internal.definitions (signature false).name =
      some (.tree (Runtime.function model (signature false))))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode) (arrays : ArrayAccess.Valid pointer buffer n n)
    (readable : References heap pointer n.toNat references) (inside : bad < n.toNat)
    (prior : ∀ i < bad, (references i).toNat ≤ 2) (invalid : ¬ (references bad).toNat ≤ 2) :
    GuardedCalls.FailureSite program
      (.calling (signature false).name (arguments (some p) pointer buffer n n) heap .done)
      heap p "Unknown value reference" := by
  have guarded := get_guard_run model heap p pointer buffer n n kind mode hk hm allowed
  rw [if_pos arrays] at guarded
  obtain ⟨types, entered⟩ := CCalls.Events.body_prefix_reaches program (Runtime.function model (signature false))
    (arguments (some p) pointer buffer n n) (parameters (some p) pointer buffer n n)
    (locals p pointer buffer n n) heap heap afterGuard .done 4
    defined (parameters_bound false _ _ _ _ _) (BodyEmbedding.body_closed model (signature false)) guarded
  let env := locals p pointer buffer n n
  let typed := bindType types "k" .size
  have initialized := counter_initialize env types heap "k"
    (loop "k" (Runtime.v "nValueReferences") [validation] :: afterValidation)
    (by simp [env, locals, parameters, CBody.bind]) (by rfl)
  have rejected := validation_rejects program env typed heap pointer n.toNat bad references afterValidation
    "fmi3Status" .done inside n.toNat_lt_size (by simp [typed, bindType])
    (by simp [env, locals, parameters, CBody.bind, resolve])
    (by simp [env, locals, parameters, CBody.bind, resolve]) readable prior invalid
  refine ⟨counterEnv env "k" bad, typed,
    counterStep "k" :: loop "k" (Runtime.v "nValueReferences") [validation] :: afterValidation,
    entered.trans (.next (CCalls.Events.body_step program initialized "fmi3Status" .done) rejected), ?_, ?_⟩
  · simp [counterEnv, env, locals, parameters, CBody.bind]
  · simp [counterEnv, env, locals, parameters, CBody.bind, resolve]

end Rumoca.FMI3.Float64Calls

noncomputable section
namespace Rumoca.FMI3.Float64Calls
open CTree CMemory

inductive GetFailure where | arrays | reference
  deriving DecidableEq

def failureMessage : GetFailure → String
  | .arrays => "Invalid Float64 array lengths or pointers"
  | .reference => "Unknown value reference"

/-- The specification classifies arguments and the readable input snapshot,
without executing the generated validation loop. -/
def FailureCondition (reason : GetFailure) (input buffer : Option Address)
    (n m : UInt64) (references : Nat → UInt32) : Prop :=
  match reason with
  | .arrays => ¬ ArrayAccess.Valid input buffer n m
  | .reference => ArrayAccess.Valid input buffer n m ∧
      ∃ bad, bad < n.toNat ∧ ¬ (references bad).toNat ≤ 2 ∧
        ∀ i < bad, (references i).toNat ≤ 2

theorem query_cases (handle input buffer : Option Address) (n m : UInt64) (references : Nat → UInt32) :
    handle = none ∨ ∃ p, handle = some p ∧
      ((n = 0 ∧ m = 0) ∨
        (∃ inputAddress outputAddress, input = some inputAddress ∧ buffer = some outputAddress ∧
          n = m ∧ ∀ i < n.toNat, (references i).toNat ≤ 2) ∨
        ∃ reason, FailureCondition reason input buffer n m references) := by
  cases handle with
  | none => exact Or.inl rfl
  | some p =>
      refine Or.inr ⟨p, rfl, ?_⟩
      by_cases arrays : ArrayAccess.Valid input buffer n m
      · have same : n = m := UInt64.toNat_inj.mp arrays.1
        by_cases zero : n.toNat = 0
        · have nz : n = 0 := UInt64.toNat_inj.mp zero
          exact Or.inl ⟨nz, same ▸ nz⟩
        · rcases reference_cases references n.toNat with valid | bad
          · have ip : input ≠ none := arrays.2.1.resolve_left zero
            have op : buffer ≠ none := arrays.2.2.resolve_left (by simpa [same] using zero)
            cases input with
            | none => exact False.elim (ip rfl)
            | some inputAddress =>
                cases buffer with
                | none => exact False.elim (op rfl)
                | some outputAddress => exact Or.inr (Or.inl ⟨_, _, rfl, rfl, same, valid⟩)
          · exact Or.inr (Or.inr ⟨.reference, arrays, bad⟩)
      · exact Or.inr (Or.inr ⟨.arrays, arrays⟩)

theorem failure_unique (first : FailureCondition a input buffer n m references)
    (second : FailureCondition b input buffer n m references) : a = b := by
  cases a <;> cases b <;> simp_all [FailureCondition]

section
variable [static : StaticLiterals]
private local instance classifiedErrorInterface : CInterface := cInterface static.addresses

theorem failure_site (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (p : Address) (input buffer : Option Address) (n m : UInt64)
    (references : Nat → UInt32) (kind : Kind) (mode : Mode) (reason : GetFailure)
    (defined : program.internal.definitions (signature false).name =
      some (.tree (Runtime.function model (signature false))))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode)
    (readable : reason = .reference → References heap input n.toNat references)
    (condition : FailureCondition reason input buffer n m references) :
    GuardedCalls.FailureSite program
      (.calling (signature false).name (arguments (some p) input buffer n m) heap .done)
      heap p (failureMessage reason) := by
  cases reason with
  | arrays => exact get_array_error_site model program heap p input buffer n m kind mode defined hk hm allowed condition
  | reference =>
      obtain ⟨arrays, bad, inside, invalid, prior⟩ := condition
      have same : n = m := UInt64.toNat_inj.mp arrays.1
      subst m
      exact get_reference_error_site model program heap p input buffer n references kind mode bad
        defined hk hm allowed arrays (readable rfl) inside prior invalid

end
end Rumoca.FMI3.Float64Calls
