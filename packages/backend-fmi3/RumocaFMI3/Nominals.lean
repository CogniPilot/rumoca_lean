import RumocaFMI3.ErrorCalls
import RumocaC.BodyEvents

/-! Complete successful and null-instance nominal queries in the shared C machine.
The default is decoded binary64 one, with exact output storage and frame guarantees. -/
noncomputable section
namespace Rumoca.FMI3.Nominals
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses
open CTree CMemory CBody

def written (heap : Heap) (buffer : Address) : Heap :=
  replace heap buffer ⟨.float64, true, some (.finite Binary64.one)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem body_run (model : Solve.FMI3Model source)
    (heap : Heap) (p buffer : Address) (kind : Kind) (mode : Mode) (old : Option Value)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getNominals kind mode)
    (storage : heap buffer = some ⟨.float64, true, old⟩) :
    run 6 (.running (Runtime.body model ErrorCalls.nominalSignature)
      (ErrorCalls.nominalEnv p (some buffer) 1) heap) =
      some (.returned ⟨.integer 0, written heap buffer⟩) := by
  let tail := ErrorCalls.nominalRest
  have accepted := LifecycleGuard.accept (ErrorCalls.nominalEnv p (some buffer) 1)
    heap p .getNominals kind mode tail
    (by simp [ErrorCalls.nominalEnv, CBody.bind])
    (by simp [ErrorCalls.nominalEnv, CBody.bind]) hk hm allowed
  have body : Runtime.body model ErrorCalls.nominalSignature = Runtime.require .getNominals ++ tail := by
    simp [Runtime.body, ErrorCalls.nominalSignature, tail, ErrorCalls.nominalRest]
  rw [body, show 6 = 3 + 3 from rfl, run_add, accepted]
  simp [tail, ErrorCalls.nominalRest, Runtime.scalarAccessCheck, Runtime.reject, Runtime.branch,
    Runtime.ret, Runtime.ok, Runtime.either, Runtime.nev, Runtime.negate, Runtime.v, Runtime.n,
    run, next, eval, lvalue, ErrorCalls.nominalEnv, CBody.bind, resolve, constants,
    CBody.cast, convert, comparison, boolean, Value.truth, Value.address, store, storage, written]

theorem call_behaviors (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (p buffer : Address) (kind : Kind) (mode : Mode) (old : Option Value)
    (defined : program.internal.definitions ErrorCalls.nominalSignature.name =
      some (.tree (Runtime.function model ErrorCalls.nominalSignature)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getNominals kind mode)
    (storage : heap buffer = some ⟨.float64, true, old⟩) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling ErrorCalls.nominalSignature.name (ErrorCalls.nominalArguments p (some buffer) 1)
        heap .done) behavior ↔ behavior = .terminates [] ⟨.integer 0, written heap buffer⟩ := by
  apply CCalls.Events.body_call_behaviors program (Runtime.function model ErrorCalls.nominalSignature)
    (ErrorCalls.nominalArguments p (some buffer) 1) (ErrorCalls.nominalEnv p (some buffer) 1)
    heap ⟨.integer 0, written heap buffer⟩ (.integer 0) 6 defined
    (ErrorCalls.nominal_parameters p (some buffer) 1)
    (BodyEmbedding.body_closed model ErrorCalls.nominalSignature)
    (body_run model heap p buffer kind mode old hk hm allowed storage)
  rfl

omit static in
theorem frame (heap : Heap) (buffer q : Address) (different : q ≠ buffer) :
    written heap buffer q = heap q := replace_other _ _ _ _ different

omit static in
theorem stored (heap : Heap) (buffer : Address) :
    load (written heap buffer) buffer = some (.finite Binary64.one) := by
  simp [written, load, Value.finite, convert]

def nullEnv (buffer : Option Address) (count : UInt64) : Locals :=
  CBody.bind (CBody.bind (CBody.bind (fun _ => none) "nContinuousStates" (.integer count.toNat))
    "nominals" (.pointer buffer)) "instance" (.pointer none)

theorem null_parameters (buffer : Option Address) (count : UInt64) :
    CCalls.parameters ErrorCalls.nominalSignature.parameters
      [.pointer none, .pointer buffer, .integer count.toNat] = some (nullEnv buffer count) := by
  have converted : CBody.cast "size_t" (.integer count.toNat) = some (.integer count.toNat) :=
    CLoops.Calls.cast_of_type "size_t" .size _ _ (by rfl) (CLoops.convert_size_nat _ count.toNat_lt_size)
  simp only [ErrorCalls.nominalSignature, CCalls.parameters,
    CCalls.parameterType, Bool.false_eq_true, ↓reduceIte, converted]
  rfl

theorem null_body (model : Solve.FMI3Model source) (heap : Heap) (buffer : Option Address) (count : UInt64) :
    run 3 (.running (Runtime.body model ErrorCalls.nominalSignature) (nullEnv buffer count) heap) =
      some (.returned ⟨.integer 3, heap⟩) := by
  simp [Runtime.body, ErrorCalls.nominalSignature, Runtime.require, Runtime.instancePrefix,
    Runtime.branch, Runtime.negate, Runtime.v, Runtime.ret, run, next, eval, nullEnv,
    CBody.bind, resolve, constants, CBody.cast, convert, Value.truth, boolean]

theorem null_behaviors (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (buffer : Option Address) (count : UInt64)
    (defined : program.internal.definitions ErrorCalls.nominalSignature.name =
      some (.tree (Runtime.function model ErrorCalls.nominalSignature))) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling ErrorCalls.nominalSignature.name [.pointer none, .pointer buffer, .integer count.toNat] heap .done)
      behavior ↔ behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  exact CCalls.Events.body_call_behaviors program (Runtime.function model ErrorCalls.nominalSignature)
    [.pointer none, .pointer buffer, .integer count.toNat] (nullEnv buffer count) heap
    ⟨.integer 3, heap⟩ (.integer 3) 3 defined (null_parameters buffer count)
    (BodyEmbedding.body_closed model ErrorCalls.nominalSignature) (null_body model heap buffer count) rfl behavior

omit static in
/-- The modeled result contains the exact positive real nominal, not merely
an encoding named one. This connects successful C storage with the XML default. -/
theorem stored_default (heap : Heap) (buffer : Address) :
    load (written heap buffer) buffer = some (.finite Binary64.one) ∧
    Binary64.value Binary64.one = 1 ∧ 0 < Binary64.value Binary64.one := by
  refine ⟨stored heap buffer, Binary64.value_one, ?_⟩
  rw [Binary64.value_one]
  exact zero_lt_one

end Rumoca.FMI3.Nominals
