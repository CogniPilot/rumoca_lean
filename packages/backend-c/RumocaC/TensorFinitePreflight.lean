import RumocaC.TensorFiniteScan
import RumocaC.TensorFinitePreflightCode

/-! Read-only finiteness preflight for a counted expression. The expression
may compute a result rather than load an output buffer. Its evaluation premise
ties every runtime coordinate to the prepared numerical result; one scalar
local suffices without tensor scratch storage, scalarization, or interface policy. -/
noncomputable section
namespace Rumoca.CTensor.FinitePreflight
open CTree CMemory CMemory.EncodedTensor
set_option maxRecDepth 10000

def sample (values : Bits shape) (k : Nat) : Value :=
  if h : 0 < k ∧ k ≤ shape.volume then .float64 values[k - 1]
  else .finite (CBody.decimalValue false 0 0)

theorem sample_succ (values : Bits shape) (k : Nat) (inside : k < shape.volume) :
    sample values (k + 1) = .float64 values[k] := by
  simp [sample, show 0 < k + 1 ∧ k + 1 ≤ shape.volume by omega]

def locals (parameters : CBody.Locals) (values : Bits shape) (k : Nat) : CBody.Locals :=
  CBody.bind (CBody.bind parameters "sample" (sample values k)) "valid"
    (CBody.boolean (FiniteScan.scanPrefix values k))

def localTypes (types : CLoops.Types) : CLoops.Types :=
  CLoops.bindType (CLoops.bindType (CLoops.bindType types "sample" .float64) "valid" .int32) "k" .size

variable [interface : CInterface]

theorem body_reaches (value : Expr) (values : Bits shape)
    (parameters : CBody.Locals) (types : CLoops.Types) (heap : Heap)
    (freshFlag : parameters "valid" = none) (freshCounter : parameters "k" = none)
    (freshSample : parameters "sample" = none)
    (count : parameters "count" = some (.integer shape.volume))
    (bounded : shape.volume < 2 ^ 64)
    (size_type : interface.types "size_t" = some .size)
    (int_type : interface.types "int32_t" = some .int32)
    (double_type : interface.types "double" = some .float64)
    (evaluated : ∀ i : Fin shape.volume,
      CLoops.eval (CLoops.counterEnv (locals parameters values i.val) "k" i.val)
        (localTypes types) heap value =
        some (.float64 values[i])) :
    Transition.Reaches CLoops.machine.step
      (.running (body value) parameters types heap)
      (.returned ⟨CBody.boolean (Solve.Tensor.Numerical.allFiniteBits values), heap⟩) := by
  let code := iteration value
  let initial := CBody.bind parameters "sample" (.finite (CBody.decimalValue false 0 0))
  let initialTypes := CLoops.bindType types "sample" .float64
  have initialized := CLoops.declare_local initial initialTypes heap "int32_t" "valid" (.nat 1)
    (CLoops.counted "k" (.id "count") code ++ [.ret (some (.id "valid"))])
    .int32 (.integer 1) (.integer 1) int_type (by simp [initial, CBody.bind, freshFlag]) rfl (by decide)
  have counter := CLoops.counter_initialize (locals parameters values 0)
    (CLoops.bindType initialTypes "valid" .int32) heap "k"
    [CLoops.loop "k" (.id "count") code, .ret (some (.id "valid"))]
    (by simp [locals, CBody.bind, freshCounter]) size_type
  have loop := CLoops.loop_reaches "k" (.id "count") code [.ret (some (.id "valid"))]
    (locals parameters values) (localTypes types) (fun _ => heap) shape.volume
    (by simp [localTypes, CLoops.bindType]) bounded
    (by simp [code, iteration, FiniteScan.iterationFor, CLoops.noDeclarations])
    (by
      intro i _
      simp [CBody.eval, CBody.evalWith, CBody.resolve, CLoops.counterEnv, CBody.bind,
        locals, count]) (by
      intro i inside
      let before := CLoops.counterEnv (locals parameters values i) "k" i
      let after := CBody.bind before "sample" (.float64 values[i])
      let rest := CLoops.counterStep "k" :: CLoops.loop "k" (.id "count") code ::
        [.ret (some (.id "valid"))]
      have assigned := CLoops.assign_local before (localTypes types) heap "sample" value
        (FiniteScan.iterationFor (.id "sample") ++ rest) (sample values i)
        (.float64 values[i]) (.float64 values[i]) .float64
        (by simp [before, CLoops.counterEnv, locals, CBody.bind])
        (by simp [localTypes, CLoops.bindType]) (evaluated ⟨i, inside⟩) rfl
      have iterated := FiniteScan.iterationFor_reaches (.id "sample")
        after (localTypes types) heap
        (CLoops.counterStep "k" :: CLoops.loop "k" (.id "count") code ::
          [.ret (some (.id "valid"))])
        values[i] (FiniteScan.scanPrefix values i)
        (by simp [CBody.eval, CBody.evalWith, CBody.resolve, after, CBody.bind])
        (by simp [after, before, CLoops.counterEnv, locals, CBody.bind])
        (by simp [localTypes, CLoops.bindType])
      have updated :
          CBody.bind after "valid"
            (CBody.boolean (FiniteScan.scanPrefix values i && Float64.finiteBits values[i])) =
          CLoops.counterEnv (locals parameters values (i + 1)) "k" i := by
        funext name
        by_cases flag : name = "valid"
        · subst name
          simp [after, CLoops.counterEnv, locals, CBody.bind, FiniteScan.scanPrefix, inside]
        · by_cases counter : name = "k"
          · subst name
            simp [after, before, CLoops.counterEnv, CBody.bind]
          · by_cases scalar : name = "sample"
            · subst name
              simp [after, CLoops.counterEnv, locals, CBody.bind, sample_succ values i inside]
            · simp [after, before, CLoops.counterEnv, locals, CBody.bind, flag, counter, scalar]
      exact .next assigned (by simpa only [updated] using iterated))
  have returned : CLoops.next
      (.running [.ret (some (.id "valid"))]
        (CLoops.counterEnv (locals parameters values shape.volume) "k" shape.volume)
        (localTypes types) heap) =
      some (.returned ⟨CBody.boolean (Solve.Tensor.Numerical.allFiniteBits values), heap⟩) := by
    simp [CLoops.next, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions,
      CBody.eval, CBody.evalWith, CBody.resolve, CLoops.counterEnv, locals, CBody.bind,
      FiniteScan.prefix_full]
  have start : CLoops.next
      (.running (.declare "int32_t" "valid" (.nat 1) ::
        (CLoops.counted "k" (.id "count") code ++ [.ret (some (.id "valid"))]))
        initial initialTypes heap) =
      some (.running (CLoops.counted "k" (.id "count") code ++ [.ret (some (.id "valid"))])
        (locals parameters values 0) (CLoops.bindType initialTypes "valid" .int32) heap) := by
    simpa only [locals, sample, Nat.lt_irrefl, false_and, ↓reduceDIte, FiniteScan.scanPrefix,
      CBody.boolean] using initialized
  have scalar := CLoops.declare_local parameters types heap "double" "sample" (.decimal false 0 0)
    (.declare "int32_t" "valid" (.nat 1) ::
      (CLoops.counted "k" (.id "count") code ++ [.ret (some (.id "valid"))]))
    .float64 (.finite (CBody.decimalValue false 0 0)) (.finite (CBody.decimalValue false 0 0))
    double_type freshSample rfl rfl
  exact .next scalar (.next start (.next counter (loop.trans (.next returned (.refl _)))))

end Rumoca.CTensor.FinitePreflight
