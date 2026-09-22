import RumocaC.CallDeclarationPrefix
import RumocaCore.Real.Floor
import RumocaC.CallCasts
import RumocaC.CallEvents

/-! Finite C floor and a supplied rounding-environment observation through
the ordinary typed call scheduler. Native libc/fenv correspondence and floating
exception flags remain explicit external boundaries. No return-success premise
is required by the complete-call theorems. -/
noncomputable section
namespace Rumoca.CMathCalls
open CMemory CTree
variable [interface : CInterface]

def floorSignature : Signature := ⟨"double", "floor", [⟨"double", "x", false⟩]⟩
def roundingSignature : Signature := ⟨"int", "fegetround", []⟩

omit interface in
theorem finite_injective : Function.Injective Value.finite := by
  intro x y same
  have bits := Value.float64.inj same
  have decoded := congrArg Float64.decode bits
  simpa only [Float64.decode_finite, Float64.Number.finite.injEq] using decoded

def floorExternal (double : interface.types "double" = some .float64) :
    CCalls.Events.External E where
  signature := floorSignature
  execute args before events result after := ∃ x : Binary64.Value,
    args = [.finite x] ∧ events = [] ∧
      result = .finite (Binary64.floorValue x) ∧ after = before
  result_typed := by
    rintro args before events result after ⟨x, rfl, rfl, rfl, rfl⟩
    exact CCalls.Casts.valueReturn "double" _ _ (by decide)
      (CCalls.Casts.named "double" .float64 _ _ double rfl)
  readonly := by
    rintro args before events result after ⟨x, rfl, rfl, rfl, rfl⟩
    exact .refl _

/-- The mode is a supplied fenv observation, not an assertion that the caller
uses nearest rounding. All int32 observations, including failure, are allowed.
A concrete program must relate this binding to its target header/environment. -/
def roundingExternal (integer : interface.types "int" = some .int32)
    (mode : Int) (bounded : -(2^31) ≤ mode ∧ mode < 2^31) :
    CCalls.Events.External E where
  signature := roundingSignature
  execute args before events result after :=
    args = [] ∧ events = [] ∧ result = .integer mode ∧ after = before
  result_typed := by
    rintro args before events result after ⟨rfl, rfl, rfl, rfl⟩
    exact CCalls.Casts.intReturn integer mode bounded
  readonly := by
    rintro args before events result after ⟨rfl, rfl, rfl, rfl⟩
    exact .refl _

theorem floor_arguments (double : interface.types "double" = some .float64)
    (x : Binary64.Value) :
    CCalls.Events.convertedArguments floorSignature.parameters [.finite x] = some [.finite x] := by
  simp [CCalls.Events.convertedArguments, floorSignature, CCalls.parameters,
    CCalls.parameterType, CBody.cast, CBody.bind, double, convert, Value.finite]

theorem rounding_arguments :
    CCalls.Events.convertedArguments roundingSignature.parameters [] = some [] := by rfl

theorem floor_effect (double : interface.types "double" = some .float64)
    (x : Binary64.Value) :
    (floorExternal (E := E) double).execute [.finite x] before events result after ↔
      events = [] ∧ result = .finite (Binary64.floorValue x) ∧ after = before := by
  constructor
  · rintro ⟨y, args, rfl, rfl, rfl⟩
    have same := finite_injective (List.cons.inj args).1
    subst y
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨x, rfl, rfl, rfl, rfl⟩

theorem floor_mathematical (double : interface.types "double" = some .float64)
    (x : Binary64.Value)
    (executed : (floorExternal (E := E) double).execute [.finite x] before events result after) :
    ∃ y, result = .finite y ∧ Binary64.value y = (⌊Binary64.value x⌋ : ℝ) ∧
      events = [] ∧ after = before := by
  obtain ⟨rfl, rfl, rfl⟩ := (floor_effect double x).mp executed
  exact ⟨Binary64.floorValue x, rfl, Binary64.floorValue_correct x, rfl, rfl⟩

theorem floor_behaviors (program : CCalls.Events.Program E)
    (double : interface.types "double" = some .float64)
    (bound : program.externals "floor" = some (floorExternal double))
    (x : Binary64.Value) (heap : Heap) (behavior) :
    (CCalls.Events.machine program).Behaves (.calling "floor" [.finite x] heap .done) behavior ↔
      behavior = .terminates [] ⟨.finite (Binary64.floorValue x), heap⟩ := by
  exact CCalls.Events.external_behaviors program bound (floor_arguments double x)
    ((floor_effect double x).mpr ⟨rfl, rfl, rfl⟩)
    (fun _ _ _ executed => (floor_effect double x).mp executed) behavior

theorem rounding_effect (integer : interface.types "int" = some .int32)
    (mode : Int) (bounded : -(2^31) ≤ mode ∧ mode < 2^31) :
    (roundingExternal (E := E) integer mode bounded).execute [] before events result after ↔
      events = [] ∧ result = .integer mode ∧ after = before := by
  simp [roundingExternal]

theorem rounding_behaviors (program : CCalls.Events.Program E)
    (integer : interface.types "int" = some .int32)
    (mode : Int) (bounded : -(2^31) ≤ mode ∧ mode < 2^31)
    (bound : program.externals "fegetround" = some (roundingExternal integer mode bounded))
    (heap : Heap) (behavior) :
    (CCalls.Events.machine program).Behaves (.calling "fegetround" [] heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer mode, heap⟩ := by
  exact CCalls.Events.external_behaviors program bound rounding_arguments
    ((rounding_effect integer mode bounded).mpr ⟨rfl, rfl, rfl⟩)
    (fun _ _ _ executed => (rounding_effect integer mode bounded).mp executed) behavior

theorem floor_declaration_path (program : CCalls.Events.Program E)
    (env : CBody.Locals) (types : CLoops.Types) (heap : Heap)
    (destination : String) (argument : Expr) (x : Binary64.Value)
    (rest : List Stmt) (resultType : String) (stack : CCalls.Typed.Continuation)
    (double : interface.types "double" = some .float64)
    (fresh : env destination = none) (unshadowed : env "floor" = none)
    (named : interface.constants "floor" = none)
    (evaluated : CBody.eval env heap argument = some (.finite x))
    (found : program.externals "floor" = some (floorExternal double)) :
    Transition.Events.Prefix (CCalls.Events.machine program)
      (.body (.running (.declare "double" destination (.call (.id "floor") [argument]) :: rest)
        env types heap) resultType stack)
      []
      (.body (.running rest (CBody.bind env destination (.finite (Binary64.floorValue x)))
        (CLoops.bindType types destination .float64) heap) resultType stack) := by
  apply CCalls.Events.external_declaration_path program env types heap heap "double" destination
    "floor" [argument] [.finite x] [.finite x] rest resultType stack
    (floorExternal double) [] (.finite (Binary64.floorValue x))
    (.finite (Binary64.floorValue x)) .float64 fresh unshadowed named (by decide)
    (by simp [CCalls.arguments, CCalls.argumentsWith, CBody.legacyExpressions, evaluated])
    found (floor_arguments double x)
    ((floor_effect double x).mpr ⟨rfl, rfl, rfl⟩)
    (fun _ _ _ h => (floor_effect double x).mp h) double rfl

theorem rounding_declaration_path (program : CCalls.Events.Program E)
    (env : CBody.Locals) (types : CLoops.Types) (heap : Heap)
    (destination : String) (mode : Int) (bounded : -(2^31) ≤ mode ∧ mode < 2^31)
    (rest : List Stmt) (resultType : String) (stack : CCalls.Typed.Continuation)
    (integer : interface.types "int" = some .int32)
    (fresh : env destination = none) (unshadowed : env "fegetround" = none)
    (named : interface.constants "fegetround" = none)
    (found : program.externals "fegetround" = some (roundingExternal integer mode bounded)) :
    Transition.Events.Prefix (CCalls.Events.machine program)
      (.body (.running (.declare "int" destination (.call (.id "fegetround") []) :: rest)
        env types heap) resultType stack)
      []
      (.body (.running rest (CBody.bind env destination (.integer mode))
        (CLoops.bindType types destination .int32) heap) resultType stack) := by
  apply CCalls.Events.external_declaration_path program env types heap heap "int" destination
    "fegetround" [] [] [] rest resultType stack (roundingExternal integer mode bounded)
    [] (.integer mode) (.integer mode) .int32 fresh unshadowed named (by decide) rfl
    found rounding_arguments ((rounding_effect integer mode bounded).mpr ⟨rfl, rfl, rfl⟩)
    (fun _ _ _ h => (rounding_effect integer mode bounded).mp h) integer
    (by simp only [convert, if_pos bounded])
end Rumoca.CMathCalls
end
