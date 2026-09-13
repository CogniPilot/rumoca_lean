import RumocaFMI3.Float64SetWrite

noncomputable section
namespace Rumoca.FMI3.Float64Set
open CTree CMemory CBody CLoops Float64Calls

inductive Failure where | lifecycle | arrays | entry
  deriving DecidableEq

def failureMessage : Failure → String
  | .lifecycle => ErrorCalls.rejectionMessage
  | .arrays => "Invalid Float64 array lengths or pointers"
  | .entry => message

def Nonempty (n m : UInt64) : Prop := n.toNat ≠ 0 ∨ m.toNat ≠ 0

def FailureCondition (reason : Failure) (kind : Kind) (mode : Mode)
    (input buffer : Option Address) (n m : UInt64) (references : Nat → UInt32) (bits : Nat → BitVec 64) : Prop :=
  Nonempty n m ∧ match reason with
  | .lifecycle => ¬ Reference.Allowed .setStart kind mode
  | .arrays => Reference.Allowed .setStart kind mode ∧ ¬ ArrayAccess.Valid input buffer n m
  | .entry => Reference.Allowed .setStart kind mode ∧ ArrayAccess.Valid input buffer n m ∧
      ∃ bad, bad < n.toNat ∧ ¬ ValidEntry (references bad) (bits bad) ∧
        ∀ i < bad, ValidEntry (references i) (bits i)

theorem entry_cases (references : Nat → UInt32) (bits : Nat → BitVec 64) (n : Nat) :
    (∀ i < n, ValidEntry (references i) (bits i)) ∨
      ∃ bad, bad < n ∧ ¬ ValidEntry (references bad) (bits bad) ∧
        ∀ i < bad, ValidEntry (references i) (bits i) := by
  classical
  by_cases valid : ∀ i < n, ValidEntry (references i) (bits i)
  · exact Or.inl valid
  · have existsBad : ∃ i, i < n ∧ ¬ ValidEntry (references i) (bits i) := by simpa using valid
    refine Or.inr ⟨Nat.find existsBad, (Nat.find_spec existsBad).1, (Nat.find_spec existsBad).2, ?_⟩
    intro i before
    have smaller := Nat.find_min existsBad before
    have inside : i < n := lt_trans before (Nat.find_spec existsBad).1
    exact Classical.byContradiction (fun bad => smaller ⟨inside, bad⟩)

theorem query_cases (kind : Kind) (mode : Mode) (handle input buffer : Option Address)
    (n m : UInt64) (references : Nat → UInt32) (bits : Nat → BitVec 64) :
    handle = none ∨ ∃ p, handle = some p ∧
      ((n = 0 ∧ m = 0) ∨
        (∃ inputAddress bufferAddress, input = some inputAddress ∧ buffer = some bufferAddress ∧
          n = m ∧ 0 < n.toNat ∧ Reference.Allowed .setStart kind mode ∧
          ∀ i < n.toNat, ValidEntry (references i) (bits i)) ∨
        ∃ reason, FailureCondition reason kind mode input buffer n m references bits) := by
  cases handle with
  | none => exact Or.inl rfl
  | some p =>
      refine Or.inr ⟨p, rfl, ?_⟩
      by_cases empty : n.toNat = 0 ∧ m.toNat = 0
      · exact Or.inl ⟨UInt64.toNat_inj.mp empty.1, UInt64.toNat_inj.mp empty.2⟩
      · have nonempty : Nonempty n m := by unfold Nonempty; omega
        by_cases permitted : Reference.Allowed .setStart kind mode
        · by_cases arrays : ArrayAccess.Valid input buffer n m
          · rcases entry_cases references bits n.toNat with valid | bad
            · have same : n = m := UInt64.toNat_inj.mp arrays.1
              have positive : 0 < n.toNat := by have := arrays.1; omega
              have ip := arrays.2.1.resolve_left (by omega)
              have bp := arrays.2.2.resolve_left (by have := arrays.1; omega)
              cases input with
              | none => exact False.elim (ip rfl)
              | some inputAddress =>
                  cases buffer with
                  | none => exact False.elim (bp rfl)
                  | some bufferAddress =>
                      exact Or.inr (Or.inl ⟨_, _, rfl, rfl, same, positive, permitted, valid⟩)
            · exact Or.inr (Or.inr ⟨.entry, nonempty, permitted, arrays, bad⟩)
          · exact Or.inr (Or.inr ⟨.arrays, nonempty, permitted, arrays⟩)
        · exact Or.inr (Or.inr ⟨.lifecycle, nonempty, permitted⟩)

theorem failure_unique (first : FailureCondition a kind mode input buffer n m references bits)
    (second : FailureCondition b kind mode input buffer n m references bits) : a = b := by
  cases a <;> cases b <;> simp_all [FailureCondition]

section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

theorem lifecycle_site (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (p : Address) (input buffer : Option Address) (n m : UInt64) (kind : Kind) (mode : Mode)
    (defined : program.internal.definitions (signature true).name =
      some (.tree (Runtime.function model (signature true))))
    (nonempty : Nonempty n m)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (denied : ¬ Reference.Allowed .setStart kind mode) :
    GuardedCalls.FailureSite program
      (.calling (signature true).name (arguments (some p) input buffer n m) heap .done)
      heap p ErrorCalls.rejectionMessage := by
  have deniedBool : allowed .setStart kind mode = false :=
    Bool.eq_false_iff.mpr (fun h => denied ((allowed_correct _ _ _).mp h))
  have guarded := entry_run model heap p input buffer n m kind mode nonempty hk hm
  rw [deniedBool] at guarded
  obtain ⟨types, reached⟩ := CCalls.Events.body_prefix_reaches program (Runtime.function model (signature true))
    (arguments (some p) input buffer n m) (parameters (some p) input buffer n m) (locals p input buffer n m)
    heap heap (Runtime.fail ErrorCalls.rejectionMessage :: Runtime.setFloat64Values) .done 4
    defined (parameters_bound true _ _ _ _ _) (BodyEmbedding.body_closed model (signature true)) guarded
  refine ⟨locals p input buffer n m, types, Runtime.setFloat64Values, reached, ?_, ?_⟩
  · simp [locals, parameters, CBody.bind]
  · simp [locals, CBody.bind, resolve]

theorem array_site (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (p : Address) (input buffer : Option Address) (n m : UInt64) (kind : Kind) (mode : Mode)
    (defined : program.internal.definitions (signature true).name =
      some (.tree (Runtime.function model (signature true))))
    (nonempty : Nonempty n m)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (permitted : Reference.Allowed .setStart kind mode) (invalid : ¬ ArrayAccess.Valid input buffer n m) :
    GuardedCalls.FailureSite program
      (.calling (signature true).name (arguments (some p) input buffer n m) heap .done)
      heap p "Invalid Float64 array lengths or pointers" := by
  have guarded := guard_run model heap p input buffer n m kind mode nonempty hk hm permitted
  rw [if_neg invalid] at guarded
  obtain ⟨types, reached⟩ := CCalls.Events.body_prefix_reaches program (Runtime.function model (signature true))
    (arguments (some p) input buffer n m) (parameters (some p) input buffer n m) (locals p input buffer n m)
    heap heap (Runtime.fail "Invalid Float64 array lengths or pointers" :: afterGuard) .done 5
    defined (parameters_bound true _ _ _ _ _) (BodyEmbedding.body_closed model (signature true)) guarded
  refine ⟨locals p input buffer n m, types, afterGuard, reached, ?_, ?_⟩
  · simp [locals, parameters, CBody.bind]
  · simp [locals, CBody.bind, resolve]

theorem entry_site (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (p : Address) (input buffer : Option Address) (n : UInt64)
    (references : Nat → UInt32) (bits : Nat → BitVec 64) (kind : Kind) (mode : Mode) (bad : Nat)
    (defined : program.internal.definitions (signature true).name =
      some (.tree (Runtime.function model (signature true))))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (permitted : Reference.Allowed .setStart kind mode) (arrays : ArrayAccess.Valid input buffer n n)
    (readable : References heap input n.toNat references)
    (valuesReadable : ReadableValues heap buffer n.toNat references bits)
    (inside : bad < n.toNat) (prior : ∀ i < bad, ValidEntry (references i) (bits i))
    (invalid : ¬ ValidEntry (references bad) (bits bad)) :
    GuardedCalls.FailureSite program
      (.calling (signature true).name (arguments (some p) input buffer n n) heap .done) heap p message := by
  have guarded := guard_run model heap p input buffer n n kind mode (Or.inl (by omega)) hk hm permitted
  rw [if_pos arrays] at guarded
  obtain ⟨types, entered⟩ := CCalls.Events.body_prefix_reaches program (Runtime.function model (signature true))
    (arguments (some p) input buffer n n) (parameters (some p) input buffer n n) (locals p input buffer n n)
    heap heap afterGuard .done 5 defined (parameters_bound true _ _ _ _ _)
    (BodyEmbedding.body_closed model (signature true)) guarded
  let env := locals p input buffer n n
  let typed := bindType types "k" .size
  have initialized := counter_initialize env types heap "k"
    (loop "k" (Runtime.v "nValueReferences") [validation] :: afterValidation)
    (by simp [env, locals, parameters, CBody.bind]) (by rfl)
  have rejected := validation_rejects program env typed heap input buffer n.toNat bad references bits afterValidation
    "fmi3Status" .done inside n.toNat_lt_size (by simp [typed, bindType])
    (by simp [env, locals, parameters, CBody.bind, resolve])
    (by simp [env, locals, parameters, CBody.bind, resolve])
    (by simp [env, locals, parameters, CBody.bind, resolve]) readable valuesReadable prior invalid
  refine ⟨counterEnv env "k" bad, typed,
    counterStep "k" :: loop "k" (Runtime.v "nValueReferences") [validation] :: afterValidation,
    entered.trans (.next (CCalls.Events.body_step program initialized "fmi3Status" .done) rejected), ?_, ?_⟩
  · simp [counterEnv, env, locals, parameters, CBody.bind]
  · simp [counterEnv, env, locals, parameters, CBody.bind, resolve]

theorem failure_site (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (p : Address) (input buffer : Option Address) (n m : UInt64)
    (references : Nat → UInt32) (bits : Nat → BitVec 64) (kind : Kind) (mode : Mode) (reason : Failure)
    (defined : program.internal.definitions (signature true).name =
      some (.tree (Runtime.function model (signature true))))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (readable : reason = .entry → References heap input n.toNat references ∧
      ReadableValues heap buffer n.toNat references bits)
    (condition : FailureCondition reason kind mode input buffer n m references bits) :
    GuardedCalls.FailureSite program
      (.calling (signature true).name (arguments (some p) input buffer n m) heap .done)
      heap p (failureMessage reason) := by
  cases reason with
  | lifecycle => exact lifecycle_site model program heap p input buffer n m kind mode defined condition.1 hk hm condition.2
  | arrays => exact array_site model program heap p input buffer n m kind mode defined condition.1 hk hm condition.2.1 condition.2.2
  | entry =>
      obtain ⟨_, permitted, arrays, bad, inside, invalid, prior⟩ := condition
      have same : n = m := UInt64.toNat_inj.mp arrays.1
      subst m
      exact entry_site model program heap p input buffer n references bits kind mode bad defined hk hm permitted
        arrays (readable rfl).1 (readable rfl).2 inside prior invalid

end
end Rumoca.FMI3.Float64Set
