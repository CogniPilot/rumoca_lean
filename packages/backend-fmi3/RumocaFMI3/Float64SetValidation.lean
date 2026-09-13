import RumocaFMI3.Float64SetEntry

noncomputable section
namespace Rumoca.FMI3.Float64Set
open CTree CMemory CBody CLoops Float64Calls

def ValidEntry (reference : UInt32) (bits : BitVec 64) : Prop :=
  reference.toNat = 1 ∧ (Value.float64 bits).isFinite = some true

instance (reference : UInt32) (bits : BitVec 64) : Decidable (ValidEntry reference bits) :=
  inferInstanceAs (Decidable (reference.toNat = 1 ∧ (Value.float64 bits).isFinite = some true))

theorem valid_entry_iff (reference : UInt32) (bits : BitVec 64) :
    ValidEntry reference bits ↔ reference.toNat = 1 ∧ ∃ x : Binary64.Value, Value.float64 bits = .finite x := by
  rw [ValidEntry, Value.isFinite_true_iff]

variable [interface : CInterface]

/-- A wrong reference short-circuits before any value-array load. -/
theorem wrong_reference_step (env : Locals) (types : Types) (heap : Heap) (rest : List Stmt)
    (referenceValue : UInt32) (loaded : CBody.eval env heap reference = some (.integer referenceValue.toNat))
    (invalid : referenceValue.toNat ≠ 1) :
    CLoops.next (.running (validation :: rest) env types heap) =
      some (.running (Runtime.fail message :: rest) env types heap) := by
  have invalidInt : ¬ (referenceValue.toNat : Int) = 1 := by omega
  simp [validation, Runtime.reject, Runtime.branch, Runtime.either, Runtime.nev, Runtime.n,
    CLoops.next, CLoops.eval, CLoops.noDeclarations, Runtime.fail, Runtime.ret,
    CBody.eval, loaded, comparison, boolean, Value.truth, invalidInt]

theorem finite_check_step (env : Locals) (types : Types) (heap : Heap) (rest : List Stmt)
    (value : Value) (finite : Bool)
    (referenceLoaded : CBody.eval env heap reference = some (.integer 1))
    (valueLoaded : CBody.eval env heap output = some value) (classified : value.isFinite = some finite) :
    CLoops.next (.running (validation :: rest) env types heap) =
      some (.running (if finite then rest else Runtime.fail message :: rest) env types heap) := by
  cases finite <;>
    simp [validation, Runtime.reject, Runtime.branch, Runtime.either, Runtime.nev, Runtime.n,
      Runtime.negate, Runtime.finite, CLoops.next, CLoops.eval, CLoops.noDeclarations,
      Runtime.fail, Runtime.ret, Runtime.call, Runtime.v, CBody.eval, referenceLoaded, valueLoaded,
      classified, comparison, boolean, Value.truth]

theorem validation_step (env : Locals) (types : Types) (heap : Heap) (rest : List Stmt)
    (referenceValue : UInt32) (bits : BitVec 64)
    (referenceLoaded : CBody.eval env heap reference = some (.integer referenceValue.toNat))
    (valueLoaded : referenceValue.toNat = 1 → CBody.eval env heap output = some (.float64 bits)) :
    CLoops.next (.running (validation :: rest) env types heap) =
      some (.running (if ValidEntry referenceValue bits then rest else Runtime.fail message :: rest) env types heap) := by
  by_cases correct : referenceValue.toNat = 1
  · have loaded : CBody.eval env heap reference = some (.integer 1) := by simpa only [correct] using referenceLoaded
    rcases Value.float64_cases bits with ⟨x, same⟩ | nonfinite
    · have classified : (Value.float64 bits).isFinite = some true :=
        (Value.isFinite_true_iff _).mpr ⟨x, same⟩
      have checked := finite_check_step env types heap rest (.float64 bits) true loaded (valueLoaded correct) classified
      simpa [ValidEntry, correct, classified] using checked
    · have checked := finite_check_step env types heap rest (.float64 bits) false loaded (valueLoaded correct) nonfinite
      simpa [ValidEntry, correct, nonfinite] using checked
  · have checked := wrong_reference_step env types heap rest referenceValue referenceLoaded correct
    simpa [ValidEntry, correct] using checked

end Rumoca.FMI3.Float64Set

noncomputable section
namespace Rumoca.FMI3.Float64Set
open CTree CMemory CBody CLoops Float64Calls

/-- A value load is required only at positions whose reference selects the
state. An invalid reference short-circuits before reading that value. -/
def ReadableValues (heap : Heap) (pointer : Option Address) (n : Nat)
    (references : Nat → UInt32) (bits : Nat → BitVec 64) : Prop :=
  ∀ i < n, (references i).toNat = 1 →
    ∃ base, pointer = some base ∧ load heap (base.index i) = some (.float64 (bits i))

variable [interface : CInterface]

theorem counter_value_eval (env : Locals) (heap : Heap) (pointer : Option Address) (n i : Nat)
    (references : Nat → UInt32) (bits : Nat → BitVec 64)
    (readable : ReadableValues heap pointer n references bits) (inside : i < n)
    (correct : (references i).toNat = 1)
    (bound : resolve env "values" = some (.pointer pointer)) :
    CBody.eval (counterEnv env "k" i) heap output = some (.float64 (bits i)) := by
  obtain ⟨base, same, loaded⟩ := readable i inside correct
  have pointerBound : resolve (counterEnv env "k" i) "values" = some (.pointer (some base)) := by
    simpa [counterEnv, CBody.bind, resolve, same] using bound
  have countBound : resolve (counterEnv env "k" i) "k" = some (.integer i) := by
    simp [counterEnv, CBody.bind, resolve]
  simp [output, Runtime.v, CBody.eval, pointerBound, countBound, Value.address, loaded]

theorem validation_prefix (program : CCalls.Events.Program E) (env : Locals) (types : Types)
    (heap : Heap) (input buffer : Option Address) (n stop : Nat)
    (references : Nat → UInt32) (bits : Nat → BitVec 64)
    (rest : List Stmt) (resultType : String) (stack : CCalls.Typed.Continuation)
    (limit : stop ≤ n) (bounded : n < 2 ^ 64) (typed : types "k" = some .size)
    (count : resolve env "nValueReferences" = some (.integer n))
    (referenceBound : resolve env "valueReferences" = some (.pointer input))
    (valueBound : resolve env "values" = some (.pointer buffer))
    (readable : References heap input n references)
    (valuesReadable : ReadableValues heap buffer n references bits)
    (valid : ∀ i < stop, ValidEntry (references i) (bits i)) :
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
    have referenceLoaded := counter_reference_eval env heap input n references i readable (by omega) referenceBound
    have valueLoaded := counter_value_eval env heap buffer n i references bits valuesReadable (by omega)
      (valid i inside).1 valueBound
    have step := validation_step (counterEnv env "k" i) types heap
      (counterStep "k" :: loop "k" (Runtime.v "nValueReferences") [validation] :: rest)
      (references i) (bits i) referenceLoaded (fun _ => valueLoaded)
    rw [if_pos (valid i inside)] at step
    exact .next (CCalls.Events.body_step program step resultType stack) (.refl _)

theorem validation_reaches (program : CCalls.Events.Program E) (env : Locals) (types : Types)
    (heap : Heap) (input buffer : Option Address) (n : Nat)
    (references : Nat → UInt32) (bits : Nat → BitVec 64)
    (rest : List Stmt) (resultType : String) (stack : CCalls.Typed.Continuation)
    (bounded : n < 2 ^ 64) (typed : types "k" = some .size)
    (count : resolve env "nValueReferences" = some (.integer n))
    (referenceBound : resolve env "valueReferences" = some (.pointer input))
    (valueBound : resolve env "values" = some (.pointer buffer))
    (readable : References heap input n references)
    (valuesReadable : ReadableValues heap buffer n references bits)
    (valid : ∀ i < n, ValidEntry (references i) (bits i)) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (loop "k" (Runtime.v "nValueReferences") [validation] :: rest)
        (counterEnv env "k" 0) types heap) resultType stack)
      (.body (.running rest (counterEnv env "k" n) types heap) resultType stack) := by
  refine (validation_prefix program env types heap input buffer n n references bits rest resultType stack
    (by omega) bounded typed count referenceBound valueBound readable valuesReadable valid).trans (.next ?_ (.refl _))
  apply CCalls.Events.body_step
  apply CLoops.loop_stop _ _ _ "k" (Runtime.v "nValueReferences") [validation] rest n
  · simp [counterEnv, CBody.bind]
  · simpa [Runtime.v, CBody.eval, counterEnv, CBody.bind, resolve] using count
  · simpa using validation_closed

/-- Every invalid entry is rejected before the setter's writing loop starts.
Its short-circuit reference check retains the absence of a value-load premise
at positions that do not select the state. -/
theorem validation_rejects (program : CCalls.Events.Program E) (env : Locals) (types : Types)
    (heap : Heap) (input buffer : Option Address) (n bad : Nat)
    (references : Nat → UInt32) (bits : Nat → BitVec 64)
    (rest : List Stmt) (resultType : String) (stack : CCalls.Typed.Continuation)
    (inside : bad < n) (bounded : n < 2 ^ 64) (typed : types "k" = some .size)
    (count : resolve env "nValueReferences" = some (.integer n))
    (referenceBound : resolve env "valueReferences" = some (.pointer input))
    (valueBound : resolve env "values" = some (.pointer buffer))
    (readable : References heap input n references)
    (valuesReadable : ReadableValues heap buffer n references bits)
    (prior : ∀ i < bad, ValidEntry (references i) (bits i))
    (invalid : ¬ ValidEntry (references bad) (bits bad)) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (loop "k" (Runtime.v "nValueReferences") [validation] :: rest)
        (counterEnv env "k" 0) types heap) resultType stack)
      (.body (.running (Runtime.fail message :: counterStep "k" ::
        loop "k" (Runtime.v "nValueReferences") [validation] :: rest)
        (counterEnv env "k" bad) types heap) resultType stack) := by
  refine (validation_prefix program env types heap input buffer n bad references bits rest resultType stack
    (by omega) bounded typed count referenceBound valueBound readable valuesReadable prior).trans
    (.next (t := .body (.running (validation :: counterStep "k" ::
      loop "k" (Runtime.v "nValueReferences") [validation] :: rest)
      (counterEnv env "k" bad) types heap) resultType stack) ?_ (.next ?_ (.refl _)))
  · apply CCalls.Events.body_step
    apply CLoops.loop_enter _ _ _ "k" (Runtime.v "nValueReferences") [validation] rest bad n
    · simp [counterEnv, CBody.bind]
    · simpa [Runtime.v, CBody.eval, counterEnv, CBody.bind, resolve] using count
    · simpa using validation_closed
    · exact inside
  · have referenceLoaded := counter_reference_eval env heap input n references bad readable inside referenceBound
    have valueLoaded := fun correct => counter_value_eval env heap buffer n bad references bits valuesReadable
      inside correct valueBound
    have step := validation_step (counterEnv env "k" bad) types heap
      (counterStep "k" :: loop "k" (Runtime.v "nValueReferences") [validation] :: rest)
      (references bad) (bits bad) referenceLoaded valueLoaded
    rw [if_neg invalid] at step
    exact CCalls.Events.body_step program step resultType stack

end Rumoca.FMI3.Float64Set
