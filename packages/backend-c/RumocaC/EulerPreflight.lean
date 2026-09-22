import RumocaCore.Solve.FiniteEuler
import RumocaC.EulerPreflightCode
import RumocaC.TensorFiniteScan

/-! Shared-C target semantics for finite Euler intervals. Finite operands, possibly overflowing
results, bounded size_t iteration. No public clocks, source lowering, ABI call
lifting, actual-file contract or native floating-environment correspondence. -/
noncomputable section
namespace Rumoca.CEulerPreflight
open CTree CMemory
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096

/-- Only candidate can be nonfinite; sample always remains a finite operand. -/
structure Snapshot where
  sample : Binary64.Value
  candidate : Float64.Number
  valid : Bool

def advance (rate : Binary64.Value) (s : Snapshot) : Snapshot :=
  if s.valid then
    match Binary64.addResult s.sample rate with
    | .finite after => ⟨after, .finite after, true⟩
    | result => ⟨s.sample, result, false⟩
  else s

def snapshots (initial rate : Binary64.Value) : Nat → Snapshot
  | 0 => ⟨initial, .finite initial, true⟩
  | n + 1 => advance rate (snapshots initial rate n)

theorem snapshots_spec (initial rate : Binary64.Value) (n : Nat) :
    Solve.FiniteEuler.run initial rate n =
      if (snapshots initial rate n).valid then some (snapshots initial rate n).sample else none := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (Solve.FiniteEuler.run initial rate n).bind
      (fun before => Solve.FiniteEuler.checkedAdd before rate) =
        if (advance rate (snapshots initial rate n)).valid then
          some (advance rate (snapshots initial rate n)).sample else none
    rw [ih]
    generalize snapshots initial rate n = s
    cases hv : s.valid <;>
      simp only [advance, hv, Bool.false_eq_true, ↓reduceIte,
        Option.bind_none, Option.bind_some]
    unfold Solve.FiniteEuler.checkedAdd
    generalize Binary64.addResult s.sample rate = result
    cases result <;> rfl

def locals (base : CBody.Locals) (s : Snapshot) : CBody.Locals :=
  CBody.bind (CBody.bind (CBody.bind base "sample" (.finite s.sample))
    "candidate" (.float64 s.candidate.encode)) "valid" (CBody.boolean s.valid)

theorem counter_locals (base : CBody.Locals) (s : Snapshot) (n : Nat) :
    CLoops.counterEnv (locals base s) "n" n = locals (CLoops.counterEnv base "n" n) s := by
  funext name
  by_cases hn : name = "n"
  · subst name; simp [CLoops.counterEnv, locals, CBody.bind]
  · simp [CLoops.counterEnv, locals, CBody.bind, hn]

variable [interface : CInterface]

theorem iteration_reaches (base : CBody.Locals) (types : CLoops.Types) (heap : Heap)
    (s : Snapshot) (rate : Binary64.Value) (rest : List Stmt)
    (rate_value : base "rate" = some (.finite rate))
    (sample_type : types "sample" = some .float64)
    (candidate_type : types "candidate" = some .float64)
    (valid_type : types "valid" = some .int32) :
    Transition.Reaches CLoops.machine.step
      (.running (iteration ++ rest) (locals base s) types heap)
      (.running rest (locals base (advance rate s)) types heap) := by
  cases hv : s.valid with
  | false =>
    apply Transition.Reaches.next (t := .running rest (locals base s) types heap)
    · change CLoops.next _ = some _
      simp [iteration, guard, CLoops.next, CLoops.nextWith, CLoops.evalWith,
        CBody.legacyExpressions, CBody.eval, CBody.evalWith, CBody.resolve,
        CBody.comparison, CBody.boolean, Value.truth, CLoops.noDeclarations,
        active, copySample, CTensor.FiniteScan.iterationFor, locals, CBody.bind, hv]
    · simpa [advance, hv] using (Transition.Reaches.refl
        (step := CLoops.machine.step) (.running rest (locals base s) types heap))
  | true =>
    let env := locals base s
    let result := Binary64.addResult s.sample rate
    let assignedEnv := CBody.bind env "candidate" (.float64 result.encode)
    let classifiedEnv := CBody.bind assignedEnv "valid" (CBody.boolean (Float64.finiteBits result.encode))
    have entered : CLoops.next (.running (iteration ++ rest) env types heap) =
        some (.running (active ++ rest) env types heap) := by
      simp [iteration, guard, CLoops.next, CLoops.nextWith, CLoops.evalWith,
        CBody.legacyExpressions, CBody.eval, CBody.evalWith, CBody.resolve,
        CBody.comparison, CBody.boolean, Value.truth, CLoops.noDeclarations,
        active, copySample, CTensor.FiniteScan.iterationFor, env, locals, CBody.bind, hv]
    have evaluated : CLoops.eval env types heap
        (.bin .add (.id "sample") (.id "rate")) = some (.float64 result.encode) := by
      simp [CLoops.eval, CLoops.evalWith, sample_type, CBody.legacyExpressions,
        CBody.eval, CBody.evalWith, CBody.resolve, env, locals, CBody.bind,
        rate_value, CArithmetic.floatAdd, CCalls.finiteValue_finite, result]
    have assigned := CLoops.assign_local env types heap "candidate"
      (.bin .add (.id "sample") (.id "rate"))
      (CTensor.FiniteScan.iterationFor (.id "candidate") ++ copySample :: rest)
      (.float64 s.candidate.encode) (.float64 result.encode) (.float64 result.encode)
      .float64 (by simp [env, locals, CBody.bind]) candidate_type evaluated rfl
    have classified := CTensor.FiniteScan.iterationFor_reaches (.id "candidate")
      assignedEnv types heap (copySample :: rest) result.encode true
      (by simp [CBody.eval, CBody.evalWith, CBody.resolve, assignedEnv, CBody.bind])
      (by simp [assignedEnv, env, locals, CBody.bind, hv]) valid_type
    simp only [Bool.true_and] at classified
    have copied : Transition.Reaches CLoops.machine.step
        (.running (copySample :: rest) classifiedEnv types heap)
        (.running rest (locals base (advance rate s)) types heap) := by
      cases hr : result with
      | finite after =>
        have added : Binary64.addResult s.sample rate = .finite after := hr
        have branch : CLoops.next (.running (copySample :: rest) classifiedEnv types heap) =
            some (.running (.assign (.id "sample") (.id "candidate") :: rest)
              classifiedEnv types heap) := by
          simp [copySample, guard, CLoops.next, CLoops.nextWith, CLoops.evalWith,
            CBody.legacyExpressions, CBody.eval, CBody.evalWith, CBody.resolve,
            CBody.comparison, CBody.boolean, Value.truth, CLoops.noDeclarations,
            classifiedEnv, CBody.bind, hr, Float64.Number.isFinite]
        have copied := CLoops.assign_local classifiedEnv types heap "sample" (.id "candidate")
          rest (.finite s.sample) (.finite after) (.finite after) .float64
          (by simp [classifiedEnv, assignedEnv, env, locals, CBody.bind]) sample_type
          (by simp [CLoops.eval, CLoops.evalWith, CBody.legacyExpressions, CBody.eval,
            CBody.evalWith, CBody.resolve, classifiedEnv, assignedEnv, CBody.bind, hr]; rfl) rfl
        have same : CBody.bind classifiedEnv "sample" (.finite after) =
            locals base (advance rate s) := by
          funext name
          by_cases hs : name = "sample"
          · subst name
            simp [classifiedEnv, locals, advance, hv, added, CBody.bind]
          · simp +contextual [classifiedEnv, assignedEnv, env, locals, advance, hv, added, hr,
              CBody.bind, hs, Float64.Number.isFinite]
        exact .next branch (.next copied (by rw [same]; exact .refl _))
      | negativeInfinity | positiveInfinity | nan =>
        have added := hr
        dsimp only [result] at added
        have same : classifiedEnv = locals base (advance rate s) := by
          funext name
          simp +contextual [classifiedEnv, assignedEnv, env, locals, advance, hv, added, hr, CBody.bind,
            Float64.Number.isFinite]
        apply Transition.Reaches.next (t := .running rest classifiedEnv types heap)
        · change CLoops.next _ = some _
          simp [copySample, guard, CLoops.next, CLoops.nextWith, CLoops.evalWith,
            CBody.legacyExpressions, CBody.eval, CBody.evalWith, CBody.resolve,
            CBody.comparison, CBody.boolean, Value.truth, CLoops.noDeclarations,
            classifiedEnv, CBody.bind, hr, Float64.Number.isFinite]
        · rw [same]; exact .refl _
    exact .next entered (.next assigned (classified.trans copied))

def parameters (initial rate : Binary64.Value) (count : Nat) : CBody.Locals := fun name =>
  if name = "initial" then some (.finite initial)
  else if name = "rate" then some (.finite rate)
  else if name = "count" then some (.integer count) else none

def parameterTypes : CLoops.Types := fun name =>
  if name = "initial" then some .float64
  else if name = "rate" then some .float64
  else if name = "count" then some .size else none

def localTypes : CLoops.Types :=
  CLoops.bindType (CLoops.bindType (CLoops.bindType (CLoops.bindType parameterTypes
    "sample" .float64) "candidate" .float64) "valid" .int32) "n" .size

def finalLocals (initial rate : Binary64.Value) (count : Nat) : CBody.Locals :=
  CLoops.counterEnv (locals (parameters initial rate count) (snapshots initial rate count)) "n" count

/-- Completion exposes the final local flag and successful sample, while
preserving the exact starting heap even on numerical failure. -/
theorem segment_reaches (initial rate : Binary64.Value) (count : Nat) (heap : Heap)
    (rest : List Stmt) (bounded : count < 2 ^ 64)
    (size_type : interface.types "size_t" = some .size)
    (int_type : interface.types "int32_t" = some .int32)
    (double_type : interface.types "double" = some .float64) :
    Transition.Reaches CLoops.machine.step
      (.running (segment ++ rest) (parameters initial rate count) parameterTypes heap)
      (.running rest (finalLocals initial rate count) localTypes heap) ∧
    finalLocals initial rate count "valid" =
      some (CBody.boolean (Solve.FiniteEuler.run initial rate count).isSome) ∧
    (∀ after, Solve.FiniteEuler.run initial rate count = some after →
      finalLocals initial rate count "sample" = some (.finite after)) := by
  let base := parameters initial rate count
  let env1 := CBody.bind base "sample" (.finite initial)
  let types1 := CLoops.bindType parameterTypes "sample" .float64
  let env2 := CBody.bind env1 "candidate" (.finite initial)
  let types2 := CLoops.bindType types1 "candidate" .float64
  have sampleInit := CLoops.declare_local base parameterTypes heap "double" "sample" (.id "initial")
    (.declare "double" "candidate" (.id "initial") :: .declare "int32_t" "valid" (.nat 1) ::
      (CLoops.counted "n" (.id "count") iteration ++ rest))
    .float64 (.finite initial) (.finite initial) double_type
    (by simp [base, parameters])
    (by simp [CLoops.eval, CLoops.evalWith, CBody.legacyExpressions, CBody.eval,
      CBody.evalWith, CBody.resolve, base, parameters]) rfl
  have candidateInit := CLoops.declare_local env1 types1 heap "double" "candidate" (.id "initial")
    (.declare "int32_t" "valid" (.nat 1) :: (CLoops.counted "n" (.id "count") iteration ++ rest))
    .float64 (.finite initial) (.finite initial) double_type
    (by simp [env1, base, CBody.bind, parameters])
    (by simp [CLoops.eval, CLoops.evalWith, CBody.legacyExpressions, CBody.eval,
      CBody.evalWith, CBody.resolve, env1, base, CBody.bind, parameters]) rfl
  have flagInit := CLoops.declare_local env2 types2 heap "int32_t" "valid" (.nat 1)
    (CLoops.counted "n" (.id "count") iteration ++ rest) .int32 (.integer 1) (.integer 1)
    int_type (by simp [env2, env1, base, CBody.bind, parameters]) rfl (by decide)
  have counter := CLoops.counter_initialize (locals base (snapshots initial rate 0))
    (CLoops.bindType types2 "valid" .int32) heap "n"
    (CLoops.loop "n" (.id "count") iteration :: rest)
    (by simp [locals, base, CBody.bind, parameters]) size_type
  have loop := CLoops.loop_reaches "n" (.id "count") iteration rest
    (fun k => locals base (snapshots initial rate k)) localTypes (fun _ => heap) count
    (by simp [localTypes, CLoops.bindType]) bounded
    (by simp [iteration, active, copySample, CTensor.FiniteScan.iterationFor, CLoops.noDeclarations])
    (by
      intro k _
      simp [CBody.eval, CBody.evalWith, CBody.resolve, CLoops.counterEnv,
        locals, CBody.bind, base, parameters])
    (by
      intro k _
      have ran := iteration_reaches (CLoops.counterEnv base "n" k) localTypes heap
        (snapshots initial rate k) rate
        (CLoops.counterStep "n" :: CLoops.loop "n" (.id "count") iteration :: rest)
        (by simp [CLoops.counterEnv, CBody.bind, base, parameters])
        (by simp [localTypes, CLoops.bindType])
        (by simp [localTypes, CLoops.bindType])
        (by simp [localTypes, CLoops.bindType])
      simpa only [counter_locals, snapshots] using ran)
  refine ⟨?_, ?_, ?_⟩
  · exact .next sampleInit (.next candidateInit (.next flagInit (.next counter loop)))
  · have spec := snapshots_spec initial rate count
    rw [spec]
    cases hv : (snapshots initial rate count).valid <;>
      simp [finalLocals, CLoops.counterEnv, locals, CBody.bind, hv]
  · intro after success
    rw [snapshots_spec] at success
    cases hv : (snapshots initial rate count).valid with
    | false => simp [hv] at success
    | true =>
      have same : (snapshots initial rate count).sample = after := by
        simpa only [hv, ↓reduceIte, Option.some.injEq] using success
      simp [finalLocals, CLoops.counterEnv, locals, CBody.bind, same]

/-- Function-body semantics and its unique behavior, without assuming ABI
binding, native compilation or an actual rendered file certificate. -/
theorem function_correct (initial rate : Binary64.Value) (count : Nat) (heap : Heap)
    (bounded : count < 2 ^ 64)
    (size_type : interface.types "size_t" = some .size)
    (int_type : interface.types "int32_t" = some .int32)
    (double_type : interface.types "double" = some .float64) (behavior) :
    CLoops.machine.Behaves
      (.running function.body (parameters initial rate count) parameterTypes heap) behavior ↔
      behavior = .terminates
        ⟨CBody.boolean (Solve.FiniteEuler.run initial rate count).isSome, heap⟩ := by
  obtain ⟨ran, flag, _⟩ := segment_reaches initial rate count heap [.ret (some (.id "valid"))]
    bounded size_type int_type double_type
  have returned : CLoops.next
      (.running [.ret (some (.id "valid"))] (finalLocals initial rate count) localTypes heap) =
      some (.returned ⟨CBody.boolean (Solve.FiniteEuler.run initial rate count).isSome, heap⟩) := by
    simp [CLoops.next, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions,
      CBody.eval, CBody.evalWith, CBody.resolve, flag]
  exact CLoops.machine.behavior_iff (ran.trans (.next returned (.refl _))) rfl

end Rumoca.CEulerPreflight
