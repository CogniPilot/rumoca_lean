import RumocaFMI3.Float64Calls

noncomputable section
namespace Rumoca.FMI3.Float64Calls
open CTree CMemory CBody CLoops

/-- The finite input domain is indexed; an empty input requires no readable
pointer. No array elements are enumerated by compiler lowering. -/
def References (heap : Heap) (pointer : Option Address) (n : Nat) (values : Nat → UInt32) : Prop :=
  ∀ i < n, ∃ p, pointer = some p ∧ load heap (p.index i) = some (.integer (values i).toNat)

variable [interface : CInterface]

theorem counter_reference_eval (env : Locals) (heap : Heap) (pointer : Option Address)
    (n : Nat) (values : Nat → UInt32) (i : Nat)
    (references : References heap pointer n values) (inside : i < n)
    (bound : resolve env "valueReferences" = some (.pointer pointer)) :
    CBody.eval (counterEnv env "k" i) heap reference = some (.integer (values i).toNat) := by
  obtain ⟨p, same, loaded⟩ := references i inside
  apply reference_eval _ heap p i (values i) _ _ loaded
  · simpa [counterEnv, CBody.bind, resolve, same] using bound
  · simp [counterEnv, CBody.bind, resolve]

theorem validation_prefix (program : CCalls.Events.Program E) (env : Locals) (types : Types)
    (heap : Heap) (pointer : Option Address) (n stop : Nat) (values : Nat → UInt32)
    (rest : List Stmt) (resultType : String) (stack : CCalls.Typed.Continuation)
    (limit : stop ≤ n) (bounded : n < 2 ^ 64) (typed : types "k" = some .size)
    (count : resolve env "nValueReferences" = some (.integer n))
    (bound : resolve env "valueReferences" = some (.pointer pointer))
    (references : References heap pointer n values)
    (valid : ∀ i < stop, (values i).toNat ≤ 2) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (loop "k" (Runtime.v "nValueReferences") [validation] :: rest)
        (counterEnv env "k" 0) types heap) resultType stack)
      (.body (.running (loop "k" (Runtime.v "nValueReferences") [validation] :: rest)
        (counterEnv env "k" stop) types heap) resultType stack) := by
  apply CCalls.Events.loop_prefix program "k" (Runtime.v "nValueReferences") [validation] rest
    (fun _ => env) types (fun _ => heap) n 0 stop resultType stack (by omega) limit typed bounded
    (by simpa using validation_closed)
  · intro i inside
    simpa [Runtime.v, CBody.eval, counterEnv, CBody.bind, resolve] using count
  · intro i lower inside
    have loaded := counter_reference_eval env heap pointer n values i references (by omega) bound
    have next := validation_step (counterEnv env "k" i) types heap
      (counterStep "k" :: loop "k" (Runtime.v "nValueReferences") [validation] :: rest) (values i) loaded
    rw [if_pos (valid i inside)] at next
    exact .next (CCalls.Events.body_step program next resultType stack) (.refl _)

/-- The complete validation loop preserves the entire input heap and exits
with k equal to the requested size, including the empty/null-pointer case. -/
theorem validation_reaches (program : CCalls.Events.Program E) (env : Locals) (types : Types)
    (heap : Heap) (pointer : Option Address) (n : Nat) (values : Nat → UInt32)
    (rest : List Stmt) (resultType : String) (stack : CCalls.Typed.Continuation)
    (bounded : n < 2 ^ 64) (typed : types "k" = some .size)
    (count : resolve env "nValueReferences" = some (.integer n))
    (bound : resolve env "valueReferences" = some (.pointer pointer))
    (references : References heap pointer n values)
    (valid : ∀ i < n, (values i).toNat ≤ 2) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (loop "k" (Runtime.v "nValueReferences") [validation] :: rest)
        (counterEnv env "k" 0) types heap) resultType stack)
      (.body (.running rest (counterEnv env "k" n) types heap) resultType stack) := by
  refine (validation_prefix program env types heap pointer n n values rest resultType stack
    (by omega) bounded typed count bound references valid).trans (.next ?_ (.refl _))
  apply CCalls.Events.body_step
  apply CLoops.loop_stop _ _ _ "k" (Runtime.v "nValueReferences") [validation] rest n
  · simp [counterEnv, CBody.bind]
  · simpa [Runtime.v, CBody.eval, counterEnv, CBody.bind, resolve] using count
  · simpa using validation_closed

/-- The first invalid reference reaches the existing error statement before
any output write. No behavior of the logger is selected by this prefix proof. -/
theorem validation_rejects (program : CCalls.Events.Program E) (env : Locals) (types : Types)
    (heap : Heap) (pointer : Option Address) (n bad : Nat) (values : Nat → UInt32)
    (rest : List Stmt) (resultType : String) (stack : CCalls.Typed.Continuation)
    (inside : bad < n) (bounded : n < 2 ^ 64) (typed : types "k" = some .size)
    (count : resolve env "nValueReferences" = some (.integer n))
    (bound : resolve env "valueReferences" = some (.pointer pointer))
    (references : References heap pointer n values)
    (prior : ∀ i < bad, (values i).toNat ≤ 2) (invalid : ¬ (values bad).toNat ≤ 2) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (loop "k" (Runtime.v "nValueReferences") [validation] :: rest)
        (counterEnv env "k" 0) types heap) resultType stack)
      (.body (.running (Runtime.fail "Unknown value reference" :: counterStep "k" ::
        loop "k" (Runtime.v "nValueReferences") [validation] :: rest)
        (counterEnv env "k" bad) types heap) resultType stack) := by
  refine (validation_prefix program env types heap pointer n bad values rest resultType stack
    (by omega) bounded typed count bound references prior).trans
    (.next (t := .body (.running (validation :: counterStep "k" ::
      loop "k" (Runtime.v "nValueReferences") [validation] :: rest)
      (counterEnv env "k" bad) types heap) resultType stack) ?_ (.next ?_ (.refl _)))
  · apply CCalls.Events.body_step
    apply CLoops.loop_enter _ _ _ "k" (Runtime.v "nValueReferences") [validation] rest bad n
    · simp [counterEnv, CBody.bind]
    · simpa [Runtime.v, CBody.eval, counterEnv, CBody.bind, resolve] using count
    · simpa using validation_closed
    · exact inside
  · have loaded := counter_reference_eval env heap pointer n values bad references inside bound
    have next := validation_step (counterEnv env "k" bad) types heap
      (counterStep "k" :: loop "k" (Runtime.v "nValueReferences") [validation] :: rest) (values bad) loaded
    rw [if_neg invalid] at next
    exact CCalls.Events.body_step program next resultType stack

omit interface in
/-- Independent finite-domain classification supplies the least invalid
position; the executable loop need not be a premise of its specification. -/
theorem reference_cases (values : Nat → UInt32) (n : Nat) :
    (∀ i < n, (values i).toNat ≤ 2) ∨
      ∃ bad, bad < n ∧ ¬ (values bad).toNat ≤ 2 ∧ ∀ i < bad, (values i).toNat ≤ 2 := by
  classical
  by_cases valid : ∀ i < n, (values i).toNat ≤ 2
  · exact Or.inl valid
  · have existsBad : ∃ i, i < n ∧ ¬ (values i).toNat ≤ 2 := by simpa using valid
    refine Or.inr ⟨Nat.find existsBad, (Nat.find_spec existsBad).1, (Nat.find_spec existsBad).2, ?_⟩
    intro i before
    have smaller := Nat.find_min existsBad before
    have inside : i < n := lt_trans before (Nat.find_spec existsBad).1
    exact Classical.byContradiction (fun bad => smaller ⟨inside, bad⟩)

end Rumoca.FMI3.Float64Calls
