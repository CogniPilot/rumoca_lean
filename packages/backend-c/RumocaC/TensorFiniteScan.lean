import RumocaC.TensorFiniteScanCode
import RumocaC.TensorEncodedMemory
import RumocaC.LoopProofs
import RumocaC.TypedCallProofs

/-! Total finiteness scanning of readable encoded tensor storage. The invariant
tracks every visited coordinate, including those after a failure. The helper
has no heap writes, and neither chooses nor encodes an interface error policy.
Native `isfinite`, headers and trapping/exception configuration remain external
correspondence obligations. -/
noncomputable section
namespace Rumoca.CTensor.FiniteScan
open CTree CMemory CMemory.EncodedTensor
set_option maxRecDepth 10000

/-- Proof-only prefix invariant for the runtime loop. -/
def scanPrefix (values : Bits shape) : Nat → Bool
  | 0 => true
  | k + 1 => if h : k < shape.volume then scanPrefix values k && Float64.finiteBits values[k]
      else scanPrefix values k

theorem prefix_spec (values : Bits shape) (k : Nat) :
    scanPrefix values k = true ↔
      ∀ i : Fin shape.volume, i.val < k → Float64.finiteBits values[i] = true := by
  induction k with
  | zero => simp [scanPrefix]
  | succ k ih =>
    by_cases inside : k < shape.volume
    · rw [scanPrefix, dif_pos inside, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨previous, last⟩ i visited
        by_cases earlier : i.val < k
        · exact previous i earlier
        · have same : i = ⟨k, inside⟩ := by
            apply Fin.ext
            change i.val = k
            omega
          subst i
          exact last
      · intro visited
        exact ⟨fun i earlier => visited i (by omega), visited ⟨k, inside⟩ (Nat.lt_succ_self k)⟩
    · rw [scanPrefix, dif_neg inside, ih]
      apply forall_congr'
      intro i
      have earlier : i.val < k := by omega
      simp [earlier, show i.val < k + 1 by omega]

theorem prefix_full (values : Bits shape) :
    scanPrefix values shape.volume = Solve.Tensor.Numerical.allFiniteBits values := by
  apply Bool.eq_iff_iff.mpr
  rw [prefix_spec]
  simp only [Solve.Tensor.Numerical.allFiniteBits, Vector.all_eq_true]
  exact ⟨fun h i hi => h ⟨i, hi⟩ hi, fun h i _ => h i.val i.isLt⟩

/-- Empty inputs need no address. A nonempty input supplies exactly its readable
cells; there is no writable-storage or output-separation assumption. -/
def Readable (heap : Heap) (input : Option Address) (values : Bits shape) : Prop :=
  ∀ i : Fin shape.volume, ∃ base, input = some base ∧
    load heap (base.index i.val) = some (.float64 values[i])

theorem readable_some_iff (heap : Heap) (input : Address) (values : Bits shape) :
    Readable heap (some input) values ↔ ReadsBits heap input values := by
  constructor
  · intro readable i
    obtain ⟨base, same, read⟩ := readable i
    cases Option.some.inj same
    exact read
  · intro read i
    exact ⟨input, rfl, read i⟩

theorem readable_null_iff (heap : Heap) (values : Bits shape) :
    Readable heap none values ↔ shape.volume = 0 := by
  constructor
  · intro readable
    by_contra nonempty
    obtain ⟨base, impossible, _⟩ := readable ⟨0, by omega⟩
    cases impossible
  · intro empty i
    have inside := i.isLt
    omega

def parameters (input : Option Address) (count : Nat) : CBody.Locals := fun name =>
  if name = "values" then some (.pointer input)
  else if name = "count" then some (.integer count) else none

def parameterTypes : CLoops.Types := fun name =>
  if name = "values" then some .pointer
  else if name = "count" then some .size else none

def locals (input : Option Address) (values : Bits shape) (k : Nat) : CBody.Locals :=
  CBody.bind (parameters input shape.volume) "valid" (CBody.boolean (scanPrefix values k))

def localTypes : CLoops.Types :=
  CLoops.bindType (CLoops.bindType parameterTypes "valid" .int32) "k" .size

variable [interface : CInterface]

theorem iteration_reaches (env : CBody.Locals) (types : CLoops.Types) (heap : Heap)
    (rest : List Stmt) (bits : BitVec 64) (before : Bool)
    (loaded : CBody.eval env heap (indexed "values") = some (.float64 bits))
    (flag : env "valid" = some (CBody.boolean before))
    (typed : types "valid" = some .int32) :
    Transition.Reaches CLoops.machine.step
      (.running (iteration ++ rest) env types heap)
      (.running rest (CBody.bind env "valid" (CBody.boolean (before && Float64.finiteBits bits)))
        types heap) := by
  have classified := CMemory.Value.isFinite_bits bits
  cases finite : Float64.finiteBits bits with
  | false =>
    have branch : CLoops.next (.running (iteration ++ rest) env types heap) =
        some (.running (.assign (.id "valid") (.nat 0) :: rest) env types heap) := by
      simp [iteration, CLoops.next, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions,
        CLoops.noDeclarations, CBody.eval, CBody.evalWith, loaded, classified, finite,
        CBody.boolean, Value.truth]
    have assigned := CLoops.assign_local env types heap "valid" (.nat 0) rest
      (CBody.boolean before) (.integer 0) (.integer 0) .int32 flag typed rfl (by decide)
    simp only [Bool.and_false, CBody.boolean]
    exact .next branch (.next assigned (.refl _))
  | true =>
    have unchanged : CBody.bind env "valid" (CBody.boolean before) = env := by
      funext name
      by_cases same : name = "valid"
      · subst name; simp [CBody.bind, flag]
      · simp [CBody.bind, same]
    have branch : CLoops.next (.running (iteration ++ rest) env types heap) =
        some (.running rest env types heap) := by
      simp [iteration, CLoops.next, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions,
        CLoops.noDeclarations, CBody.eval, CBody.evalWith, loaded, classified, finite,
        CBody.boolean, Value.truth]
    rw [Bool.and_true, unchanged]
    exact .next branch (.refl _)

theorem function_reaches (input : Option Address) (values : Bits shape) (heap : Heap)
    (readable : Readable heap input values) (bounded : shape.volume < 2 ^ 64)
    (size_type : interface.types "size_t" = some .size)
    (int_type : interface.types "int32_t" = some .int32) :
    Transition.Reaches CLoops.machine.step
      (.running function.body (parameters input shape.volume) parameterTypes heap)
      (.returned ⟨CBody.boolean (Solve.Tensor.Numerical.allFiniteBits values), heap⟩) := by
  have initialized := CLoops.declare_local (parameters input shape.volume) parameterTypes heap
    "int32_t" "valid" (.nat 1)
    (CLoops.counted "k" (.id "count") iteration ++ [.ret (some (.id "valid"))])
    .int32 (.integer 1) (.integer 1) int_type (by simp [parameters]) rfl (by decide)
  have counter := CLoops.counter_initialize (locals input values 0)
    (CLoops.bindType parameterTypes "valid" .int32) heap "k"
    [CLoops.loop "k" (.id "count") iteration, .ret (some (.id "valid"))]
    (by simp [locals, CBody.bind, parameters]) size_type
  have loop := CLoops.loop_reaches "k" (.id "count") iteration [.ret (some (.id "valid"))]
    (locals input values) localTypes (fun _ => heap) shape.volume
    (by simp [localTypes, CLoops.bindType]) bounded (by simp [iteration, CLoops.noDeclarations])
    (by
      intro i _
      simp [CBody.eval, CBody.evalWith, CBody.resolve, CLoops.counterEnv, CBody.bind,
        locals, parameters]) (by
      intro i inside
      obtain ⟨base, input_eq, read⟩ := readable ⟨i, inside⟩
      have loaded : CBody.eval (CLoops.counterEnv (locals input values i) "k" i) heap
          (indexed "values") = some (.float64 values[i]) := by
        simpa [indexed, CBody.eval, CBody.evalWith, CBody.resolve, CLoops.counterEnv,
          CBody.bind, locals, parameters, input_eq, Value.address] using read
      have iterated := iteration_reaches (CLoops.counterEnv (locals input values i) "k" i)
        localTypes heap
        (CLoops.counterStep "k" :: CLoops.loop "k" (.id "count") iteration :: [.ret (some (.id "valid"))])
        values[i] (scanPrefix values i) loaded
        (by simp [CLoops.counterEnv, locals, CBody.bind])
        (by simp [localTypes, CLoops.bindType])
      have updated :
          CBody.bind (CLoops.counterEnv (locals input values i) "k" i) "valid"
            (CBody.boolean (scanPrefix values i && Float64.finiteBits values[i])) =
          CLoops.counterEnv (locals input values (i + 1)) "k" i := by
        funext name
        by_cases flag : name = "valid"
        · subst name
          simp [CLoops.counterEnv, locals, CBody.bind, scanPrefix, inside]
        · by_cases counter : name = "k"
          · subst name
            simp [CLoops.counterEnv, CBody.bind]
          · simp [CLoops.counterEnv, locals, CBody.bind, flag, counter]
      simpa only [updated] using iterated)
  have returned : CLoops.next
      (.running [.ret (some (.id "valid"))]
        (CLoops.counterEnv (locals input values shape.volume) "k" shape.volume) localTypes heap) =
      some (.returned ⟨CBody.boolean (Solve.Tensor.Numerical.allFiniteBits values), heap⟩) := by
    simp [CLoops.next, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions,
      CBody.eval, CBody.evalWith, CBody.resolve, CLoops.counterEnv, locals, CBody.bind, prefix_full]
  have start : CLoops.next
      (.running function.body (parameters input shape.volume) parameterTypes heap) =
      some (.running (CLoops.counted "k" (.id "count") iteration ++ [.ret (some (.id "valid"))])
        (locals input values 0) (CLoops.bindType parameterTypes "valid" .int32) heap) := by
    simpa only [function, locals, scanPrefix, CBody.boolean, List.cons_append, List.nil_append] using initialized
  exact .next start (.next counter (loop.trans (.next returned (.refl _))))

theorem function_correct (input : Option Address) (values : Bits shape) (heap : Heap)
    (readable : Readable heap input values) (bounded : shape.volume < 2 ^ 64)
    (size_type : interface.types "size_t" = some .size)
    (int_type : interface.types "int32_t" = some .int32) (behavior) :
    CLoops.machine.Behaves
      (.running function.body (parameters input shape.volume) parameterTypes heap) behavior ↔
      behavior = .terminates ⟨CBody.boolean (Solve.Tensor.Numerical.allFiniteBits values), heap⟩ :=
  CLoops.machine.behavior_iff (function_reaches input values heap readable bounded size_type int_type) rfl

end Rumoca.CTensor.FiniteScan
