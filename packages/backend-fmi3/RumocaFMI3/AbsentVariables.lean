import RumocaC.LoopCalls
import RumocaFMI3.GuardedCalls
import RumocaFMI3.BodyEmbedding

noncomputable section
namespace Rumoca.FMI3.AbsentVariables
open CTree CMemory CBody

/-- The currently emitted non-Float64, non-clock variable access family. -/
inductive VariableType where
  | float32 | int8 | uint8 | int16 | uint16 | int32 | uint32
  | int64 | uint64 | boolean | string | binary

def VariableType.name : VariableType → String
  | .float32 => "Float32"
  | .int8 => "Int8"
  | .uint8 => "UInt8"
  | .int16 => "Int16"
  | .uint16 => "UInt16"
  | .int32 => "Int32"
  | .uint32 => "UInt32"
  | .int64 => "Int64"
  | .uint64 => "UInt64"
  | .boolean => "Boolean"
  | .string => "String"
  | .binary => "Binary"

def VariableType.hasSizes : VariableType → Bool
  | .binary => true
  | _ => false

def signature (kind : VariableType) (write : Bool) : Signature :=
  ⟨"fmi3Status", (if write then "fmi3Set" else "fmi3Get") ++ kind.name,
    [⟨"fmi3Instance", "instance", false⟩,
     ⟨"const fmi3ValueReference", "valueReferences", true⟩,
     ⟨"size_t", "nValueReferences", false⟩] ++
    (if kind.hasSizes then [⟨if write then "const size_t" else "size_t", "valueSizes", true⟩] else []) ++
    [⟨(if write then "const fmi3" else "fmi3") ++ kind.name, "values", true⟩,
     ⟨"size_t", "nValues", false⟩]⟩

def suffix : List Stmt :=
  [Runtime.branch
    (Runtime.both (Runtime.eqv (Runtime.v "nValueReferences") (Runtime.n 0))
      (Runtime.eqv (Runtime.v "nValues") (Runtime.n 0))) [Runtime.ok],
   Runtime.fail "No variables of this type exist"]

/-- Every member uses the same suffix in the actual emitter. This does not
assume a body supplied by a caller or a replacement implementation. -/
theorem body_eq (model : Solve.FMI3Model source) (kind : VariableType) (write : Bool) :
    Runtime.body model (signature kind write) = Runtime.require .get ++ suffix := by
  cases kind <;> cases write <;>
    simp only [signature, VariableType.name, VariableType.hasSizes,
      Bool.false_eq_true, ↓reduceIte, String.reduceAppend] <;>
    unfold Runtime.body <;> split <;> first
    | (rename_i impossible; solve | simp at impossible)
    | (split <;> first | rfl | (rename_i rejected; exact (rejected (by decide +kernel)).elim))

def arguments (hasSizes : Bool) (handle references sizes values : Option Address)
    (n m : UInt64) : List Value :=
  [.pointer handle, .pointer references, .integer n.toNat] ++
  (if hasSizes then [.pointer sizes] else []) ++ [.pointer values, .integer m.toNat]

def parameters (hasSizes : Bool) (handle references sizes values : Option Address)
    (n m : UInt64) : Locals :=
  let tail := bind (bind (fun _ => none) "nValues" (.integer m.toNat)) "values" (.pointer values)
  let withSizes := if hasSizes then bind tail "valueSizes" (.pointer sizes) else tail
  bind (bind (bind withSizes "nValueReferences" (.integer n.toNat))
    "valueReferences" (.pointer references)) "instance" (.pointer handle)

variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

/-- No array elements or pointers are read when both cardinalities are zero. -/
theorem empty_body (env : Locals) (heap : Heap) (p : Address)
    (kind : Kind) (mode : Mode)
    (hi : env "instance" = some (.pointer (some p))) (hn : env "m" = none)
    (ok : env "fmi3OK" = none)
    (refs : env "nValueReferences" = some (.integer 0))
    (values : env "nValues" = some (.integer 0))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode) :
    run 5 (.running (Runtime.require .get ++ suffix) env heap) =
      some (.returned ⟨.integer 0, heap⟩) := by
  rw [show 5 = 3 + 2 from rfl, run_add,
    LifecycleGuard.accept env heap p .get kind mode suffix hi hn hk hm allowed]
  simp [suffix, run, next, Runtime.branch, Runtime.both, Runtime.eqv,
    Runtime.v, Runtime.n, Runtime.ok, Runtime.ret, eval, resolve,
    CBody.bind, constants, refs, values, ok, Value.truth, boolean, comparison]

/-- A nonempty request reaches the shared diagnostic before reading any
array element. The existing failure-call theorem supplies logger outcomes. -/
theorem nonempty_body (env : Locals) (heap : Heap) (p : Address)
    (kind : Kind) (mode : Mode) (referenceCount valueCount : Int)
    (hi : env "instance" = some (.pointer (some p))) (hn : env "m" = none)
    (refs : env "nValueReferences" = some (.integer referenceCount))
    (values : env "nValues" = some (.integer valueCount))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode)
    (nonempty : referenceCount ≠ 0 ∨ valueCount ≠ 0) :
    run 4 (.running (Runtime.require .get ++ suffix) env heap) =
      some (.running [Runtime.fail "No variables of this type exist"]
        (CBody.bind env "m" (.pointer (some p))) heap) := by
  rw [show 4 = 3 + 1 from rfl, run_add,
    LifecycleGuard.accept env heap p .get kind mode suffix hi hn hk hm allowed]
  by_cases referenceZero : referenceCount = 0
  · have valueNonzero : valueCount ≠ 0 := nonempty.resolve_left (by simpa using referenceZero)
    simp [suffix, run, next, Runtime.branch, Runtime.both, Runtime.eqv,
      Runtime.v, Runtime.n, eval, resolve, CBody.bind, refs, values,
      Value.truth, boolean, comparison, referenceZero, valueNonzero]
  · simp [suffix, run, next, Runtime.branch, Runtime.both, Runtime.eqv,
      Runtime.v, Runtime.n, eval, resolve, CBody.bind, refs,
      Value.truth, boolean, comparison, referenceZero]

theorem parameters_bound (ty : VariableType) (write : Bool)
    (handle references sizes values : Option Address) (n m : UInt64) :
    CCalls.parameters (signature ty write).parameters
      (arguments ty.hasSizes handle references sizes values n m) =
      some (parameters ty.hasSizes handle references sizes values n m) := by
  have nc : CBody.cast "size_t" (.integer n.toNat) = some (.integer n.toNat) :=
    CLoops.Calls.cast_of_type "size_t" .size _ _ rfl (CLoops.convert_size_nat _ n.toNat_lt_size)
  have mc : CBody.cast "size_t" (.integer m.toNat) = some (.integer m.toNat) :=
    CLoops.Calls.cast_of_type "size_t" .size _ _ rfl (CLoops.convert_size_nat _ m.toNat_lt_size)
  cases ty <;> cases write <;>
    simp only [signature, VariableType.name, VariableType.hasSizes, parameters, arguments,
      Bool.false_eq_true, ↓reduceIte, String.reduceAppend, List.nil_append,
      List.cons_append, CCalls.parameters, CCalls.parameterType, nc, mc] <;> rfl

/-- The complete observable public call, for every one of the 24 actual
emitted signatures and arbitrary unused pointer arguments. -/
theorem empty_behaviors (model : Solve.FMI3Model source) (ty : VariableType) (write : Bool)
    (program : CCalls.Events.Program E) (heap : Heap) (p : Address)
    (references sizes values : Option Address) (kind : Kind) (mode : Mode)
    (defined : program.internal.definitions (signature ty write).name =
      some (.tree (Runtime.function model (signature ty write))))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode) (observed) :
    (CCalls.Events.machine program).Behaves
      (.calling (signature ty write).name
        (arguments ty.hasSizes (some p) references sizes values 0 0) heap .done) observed ↔
      observed = .terminates [] ⟨.integer 0, heap⟩ := by
  have executed := empty_body (parameters ty.hasSizes (some p) references sizes values 0 0)
    heap p kind mode (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind, ite_apply])
    (by simp [parameters, CBody.bind, ite_apply]) (by simp [parameters, CBody.bind])
    (by simp [parameters, CBody.bind, ite_apply]) hk hm allowed
  rw [← body_eq model ty write] at executed
  exact CCalls.Events.body_call_behaviors program (Runtime.function model (signature ty write))
    _ _ heap _ (.integer 0) 5 defined (parameters_bound ty write _ _ _ _ _ _)
    (BodyEmbedding.body_closed model (signature ty write)) executed rfl observed

/-- Null-instance tolerance is complete authored behavior, not permission
for importers to violate FMI's argument rules. -/
theorem null_behaviors (model : Solve.FMI3Model source) (ty : VariableType) (write : Bool)
    (program : CCalls.Events.Program E) (heap : Heap)
    (references sizes values : Option Address) (n m : UInt64)
    (defined : program.internal.definitions (signature ty write).name =
      some (.tree (Runtime.function model (signature ty write)))) (observed) :
    (CCalls.Events.machine program).Behaves
      (.calling (signature ty write).name
        (arguments ty.hasSizes none references sizes values n m) heap .done) observed ↔
      observed = .terminates [] ⟨.integer 3, heap⟩ := by
  have shaped : (Runtime.function model (signature ty write)).body =
      Runtime.instancePrefix ++ Runtime.modeGuard .get :: suffix := by
    simp [Runtime.function, body_eq, Runtime.require, List.append_assoc]
  apply GuardedCalls.null_behaviors program (Runtime.function model (signature ty write))
    (Runtime.modeGuard .get :: suffix) _ (parameters ty.hasSizes none references sizes values n m)
    heap defined (parameters_bound ty write _ _ _ _ _ _) shaped rfl
    (BodyEmbedding.body_closed model (signature ty write))
  · simp [parameters, CBody.bind]
  · simp [parameters, CBody.bind, ite_apply]
  · simp [parameters, CBody.bind, ite_apply]

/-- Nonempty requests carry an executed prefix into the existing complete
failure/logger rules; no chosen error return is used as a premise. -/
theorem nonempty_prefix (model : Solve.FMI3Model source) (ty : VariableType) (write : Bool)
    (heap : Heap) (p : Address) (references sizes values : Option Address)
    (n m : UInt64) (kind : Kind) (mode : Mode)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode)
    (nonempty : n.toNat ≠ 0 ∨ m.toNat ≠ 0) :
    GuardedCalls.FailurePrefix (Runtime.function model (signature ty write))
      (arguments ty.hasSizes (some p) references sizes values n m) heap p
      "No variables of this type exist" heap := by
  let env := parameters ty.hasSizes (some p) references sizes values n m
  have executed := nonempty_body env heap p kind mode n.toNat m.toNat
    (by simp [env, parameters, CBody.bind]) (by simp [env, parameters, CBody.bind, ite_apply])
    (by simp [env, parameters, CBody.bind]) (by simp [env, parameters, CBody.bind, ite_apply])
    hk hm allowed (by omega)
  refine ⟨rfl, BodyEmbedding.body_closed model (signature ty write), env,
    CBody.bind env "m" (.pointer (some p)), [], 4,
    parameters_bound ty write _ _ _ _ _ _, ?_, ?_, ?_⟩
  · simpa only [Runtime.function, body_eq] using executed
  · simp [env, parameters, CBody.bind, ite_apply]
  · simp [CBody.bind, resolve]

end Rumoca.FMI3.AbsentVariables
end
