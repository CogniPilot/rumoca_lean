import RumocaFMI3.DebugLoggingValidation

/-! An arbitrary finite category array is read in place. All comparisons in a
valid prefix are completed before the logging flag can be written. Empty arrays
need no readable pointer; null elements remain available as rejection cases. -/
noncomputable section
namespace Rumoca.FMI3.DebugLogging
open CTree CMemory CBody CLoops CStringMemory

def Entries (heap : Heap) (pointer : Option Address) (n : Nat)
    (selected : Nat → Option Address) (bytes : Nat → List UInt8) : Prop :=
  ∀ i < n, ∃ base, pointer = some base ∧
    load heap (base.index i) = some (.pointer (selected i)) ∧
    ∀ value, selected i = some value → Contents heap value (bytes i)

def Accepted (selected : Option Address) (bytes expected : List UInt8) : Prop :=
  selected.isSome = true ∧ bytes = expected

variable [interface : CInterface]

theorem entry_eval (env : Locals) (heap : Heap) (pointer : Option Address) (n i : Nat)
    (selected : Nat → Option Address) (bytes : Nat → List UInt8)
    (entries : Entries heap pointer n selected bytes) (inside : i < n)
    (bound : env "categories" = some (.pointer pointer)) :
    CBody.eval (counterEnv env "k" i) heap category = some (.pointer (selected i)) := by
  obtain ⟨base, same, loaded, _⟩ := entries i inside
  apply category_eval _ heap base i (selected i) _ _ loaded
  · simp [counterEnv, resolve, CBody.bind, bound, same]
  · simp [counterEnv, resolve, CBody.bind]

theorem validation_prefix_equivalence (program : CCalls.Events.Program E)
    (env : Locals) (types : Types) (heap : Heap) (pointer : Option Address)
    (n stop : Nat) (selected : Nat → Option Address) (bytes : Nat → List UInt8)
    (expected : Address) (expectedBytes : List UInt8) (rest : List Stmt)
    (resultType : String) (stack : CCalls.Typed.Continuation)
    (limit : stop ≤ n) (bounded : n < 2^64)
    (counterType : types "k" = some .size)
    (count : env "nCategories" = some (.integer n))
    (array : env "categories" = some (.pointer pointer))
    (old : env "difference" = some (.integer 0))
    (differenceType : types "difference" = some .int32)
    (unshadowed : env "strcmp" = none) (named : interface.constants "strcmp" = none)
    (pointerType : interface.types "const char *" = some .pointer)
    (integer : interface.types "int" = some .int32)
    (bound : program.externals "strcmp" = some (CStringCalls.compareExternal integer))
    (literal : interface.literals "logStatus" = some expected)
    (expectedStored : Contents heap expected expectedBytes)
    (entries : Entries heap pointer n selected bytes)
    (valid : ∀ i < stop, Accepted (selected i) (bytes i) expectedBytes)
    (behavior) :
    (CCalls.Events.machine program).Behaves
      (.body (.running (validation :: rest) (counterEnv env "k" 0) types heap) resultType stack) behavior ↔
    (CCalls.Events.machine program).Behaves
      (.body (.running (validation :: rest) (counterEnv env "k" stop) types heap) resultType stack) behavior := by
  apply CCalls.Events.loop_prefix_equivalence program "k" (.id "nCategories") iteration rest
    (fun _ => env) types (fun _ => heap) n 0 stop resultType stack (by omega) limit
    counterType bounded iteration_closed
  · intro i inside
    simp [CBody.eval, CBody.evalWith, counterEnv, resolve, CBody.bind, count]
  · intro i lower inside observed
    obtain ⟨present, equal⟩ := valid i inside
    obtain ⟨base, _, _, stored⟩ := entries i (by omega)
    have loaded := entry_eval env heap pointer n i selected bytes entries (by omega) array
    cases chosen : selected i with
    | none => simp [chosen] at present
    | some value =>
      have content : Contents heap value expectedBytes := equal ▸ stored value chosen
      have unchanged : CBody.bind (counterEnv env "k" i) "difference" (.integer 0) = counterEnv env "k" i := by
        funext key
        by_cases same : key = "difference" <;> simp [counterEnv, CBody.bind, old, same]
      rw [chosen] at loaded
      simpa only [unchanged] using iteration_valid_equivalence program (counterEnv env "k" i)
        types heap value expected expectedBytes (.integer 0)
        (counterStep "k" :: validation :: rest) resultType stack pointerType integer
        (by simp [counterEnv, CBody.bind, old]) differenceType
        (by simp [counterEnv, CBody.bind, unshadowed]) named bound loaded literal content expectedStored observed

theorem validation_valid_equivalence (program : CCalls.Events.Program E)
    (env : Locals) (types : Types) (heap : Heap) (pointer : Option Address)
    (n : Nat) (selected : Nat → Option Address) (bytes : Nat → List UInt8)
    (expected : Address) (expectedBytes : List UInt8) (rest : List Stmt)
    (resultType : String) (stack : CCalls.Typed.Continuation)
    (bounded : n < 2^64) (counterType : types "k" = some .size)
    (count : env "nCategories" = some (.integer n))
    (array : env "categories" = some (.pointer pointer))
    (old : env "difference" = some (.integer 0))
    (differenceType : types "difference" = some .int32)
    (unshadowed : env "strcmp" = none) (named : interface.constants "strcmp" = none)
    (pointerType : interface.types "const char *" = some .pointer)
    (integer : interface.types "int" = some .int32)
    (bound : program.externals "strcmp" = some (CStringCalls.compareExternal integer))
    (literal : interface.literals "logStatus" = some expected)
    (expectedStored : Contents heap expected expectedBytes)
    (entries : Entries heap pointer n selected bytes)
    (valid : ∀ i < n, Accepted (selected i) (bytes i) expectedBytes)
    (behavior) :
    (CCalls.Events.machine program).Behaves
      (.body (.running (validation :: rest) (counterEnv env "k" 0) types heap) resultType stack) behavior ↔
    (CCalls.Events.machine program).Behaves
      (.body (.running rest (counterEnv env "k" n) types heap) resultType stack) behavior := by
  apply (validation_prefix_equivalence program env types heap pointer n n selected bytes expected
    expectedBytes rest resultType stack (by omega) bounded counterType count array old differenceType
    unshadowed named pointerType integer bound literal expectedStored entries valid behavior).trans
  have stopped := CLoops.loop_stop (counterEnv env "k" n) types heap "k" (.id "nCategories")
    iteration rest n (by simp [counterEnv, CBody.bind])
    (by simp [CBody.eval, CBody.evalWith, counterEnv, CBody.bind, resolve, count]) iteration_closed
  exact CCalls.Events.internal_prefix_behaviors program
    (.next (CCalls.Events.body_step program stopped resultType stack) (.refl _)) behavior

end Rumoca.FMI3.DebugLogging
end
