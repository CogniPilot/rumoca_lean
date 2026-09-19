import RumocaFMI3.CallPolicy
import RumocaFMI3.ConstantFunctions

/-! Classify and bound every call in the constant-rate (`G01`) FMI adapter function
list against a named boundary set, and instantiate the reusable no-heap and acyclic
call-graph policy. The constant bodies dispatch the same runtime combinators the
scalar adapter uses, call the shared release/factory helpers, and call the three
prepared constant kernel entries `rumoca_constant_rhs`/`rumoca_constant_step`/
`rumoca_constant_sample` directly; no generated call graph names an allocation entry
point. Foreign/native and function-pointer boundaries remain explicit, as for the
scalar adapter. -/
namespace Rumoca.FMI3.ConstantCallPolicy
open CTree CCalls CCallPolicy
open Rumoca.FMI3.CallPolicy (accepted classify bUnit functionRank)
open Rumoca.Tensor (Shape)
set_option autoImplicit false
variable {source : AST.Model} {n : Nat}

/-- The constant adapter admits every callee the scalar classification admits, plus
the three prepared constant kernel entries `rumoca_constant_rhs`/
`rumoca_constant_step`/`rumoca_constant_sample`, which the constant derivative
getter and step call directly. -/
def acceptedC : Expr → Bool
  | .id name => accepted (.id name) || name == "rumoca_constant_rhs"
      || name == "rumoca_constant_step" || name == "rumoca_constant_sample"
  | e => accepted e

/-- Every scalar-accepted callee is constant-accepted. -/
theorem accepted_acceptedC (e : Expr) (acc : accepted e = true) : acceptedC e = true := by
  cases e <;> simp_all [acceptedC]

/-- Monotonicity of the syntactic admission predicate along the call inventory. -/
theorem statementAdmits_mono {p q : Expr → Prop} (imp : ∀ e, p e → q e) (stmt : Stmt)
    (h : StatementAdmits p stmt) : StatementAdmits q stmt :=
  (statement_calls_complete q stmt).mp
    (fun callee mem => imp callee ((statement_calls_complete p stmt).mpr h callee mem))

macro "cadmit" : tactic => `(tactic| (
  simp only [TensorReset.function, TensorReset.body, TensorReset.resetTail, TensorReset.bookkeepingTail,
    TensorReset.zeroBody,
    TensorNominals.function, TensorNominals.body, TensorNominals.nominalTail, TensorNominals.oneBody,
    TensorNominals.countReject,
    TensorCountQueries.function, TensorCountQueries.body, TensorCountQueries.rest,
    TensorSetTime.function, TensorSetTime.body, TensorSetTime.tail, TensorSetTime.finiteReject,
    TensorLifecycleModes.function, TensorLifecycleModes.body, TensorLifecycleModes.tail,
    TensorLifecycleModes.Phase.command,
    TensorFree.function,
    TensorFactory.function, TensorFactory.code, TensorFactory.initializeInstance,
    TensorInstanceInit.code, TensorInstanceInit.slotStore, TensorInstanceInit.metaCode,
    TensorInstanceInit.stateTail,
    FactoryPrefix.body, FactoryPrefix.entry,
    TensorFloat64.getFunction, TensorFloat64.getBody, TensorFloat64.getRest, TensorFloat64.getDispatch,
    TensorFloat64.getDispatch1, TensorFloat64.getDispatch2, TensorFloat64.getDispatch3,
    TensorFloat64.getDispatch4, TensorFloat64.getArm, TensorFloat64.getOutputArm,
    TensorFloat64.getLoopSuffix, TensorFloat64.basicReject, TensorFloat64.countReject,
    TensorFloat64.memberPointer, TensorFloat64.vr0,
    TensorFloat64.setFunction, TensorFloat64.setBody, TensorFloat64.setRest, TensorFloat64.setDispatch,
    TensorFloat64.setDispatch2, TensorFloat64.setArm, TensorFloat64.setLoopSuffix,
    TensorFloat64.validateBody, TensorFloat64.getCopyBody, TensorFloat64.setCopyBody,
    TensorFloat64.srcCell, TensorFloat64.dstCell,
    Float64Calls.output, Float64Calls.reference,
    TensorContinuousStates.getFunction, TensorContinuousStates.getBody, TensorContinuousStates.getTail,
    TensorContinuousStates.setFunction, TensorContinuousStates.setBody, TensorContinuousStates.setTail,
    TensorContinuousStates.derivFunction, TensorContinuousStates.derivBody,
    TensorContinuousStates.derivTail,
    TensorContinuousStates.derivCopyTail, TensorContinuousStates.derivCountReject,
    TensorFloat64.getLoopSuffix, TensorFloat64.setLoopSuffix,
    TensorContinuousStates.derivEntryArgs, TensorContinuousStates.jacobianEntryArgs,
    TensorContinuousStates.jacobianCall, TensorContinuousStates.countReject,
    TensorDoStep.function, TensorDoStep.doStepBody, TensorDoStep.tensorStepSolve,
    TensorDoStep.internalBody, TensorDoStep.eulerTail, TensorDoStep.eulerBody,
    TensorDoStep.stepBodyT, TensorDoStep.timeAdvance, TensorDoStep.stepPublishTail,
    TensorDoStep.stepBody, TensorDoStep.oneExpr, TensorDoStep.jacobianTail, CAlgorithm.literal,
    ConstantFloat64.getFunction, ConstantFloat64.getBody, ConstantFloat64.getRest,
    ConstantFloat64.getDispatch, ConstantFloat64.getDispatch1, ConstantFloat64.getDispatch2,
    ConstantFloat64.setFunction, ConstantFloat64.setBody, ConstantFloat64.setRest,
    ConstantFloat64.setDispatch,
    ConstantDerivative.derivFunction, ConstantDerivative.derivBody, ConstantDerivative.entryArgs,
    ConstantDoStep.function, ConstantDoStep.doStepBody, ConstantDoStep.stepSolve,
    ConstantDoStep.stepBody, ConstantDoStep.stepBodyT,
    TensorInstance.timeName, TensorInstance.stateName, TensorInstance.inputName,
    TensorInstance.derivativeName, TensorInstance.outputName]
  fmi_literal_calls
  all_goals simp [StatementAdmits, ExpressionAdmits, acceptedC, accepted, classify,
    Runtime.finite, Runtime.invalidTime, Runtime.allowedExpression, permittedModes,
    Runtime.any, Runtime.all, Runtime.eqv, Runtime.nev, Runtime.both, Runtime.either,
    Runtime.lt, Runtime.le, Runtime.gt, Runtime.ge, Runtime.negate, Runtime.region, Runtime.x,
    Runtime.field, Runtime.setMode, Runtime.mode, Runtime.v, Runtime.n, Runtime.call, Runtime.out,
    Runtime.put, Runtime.pointerCheck, Runtime.scalarAccessCheck, Runtime.countLoop,
    CLoops.loop, CLoops.counterStep]
  done))

set_option maxHeartbeats 4000000 in
/-- Every constant adapter function body admits only constant-accepted callees. The
dispatched constant and reused tensor bodies call the runtime combinators and the
three prepared constant kernel entries; every other signature reuses the scalar
body, whose admission is the scalar `body_policy` widened to the constant boundary. -/
theorem body_admits (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sig : Signature) :
    ∀ stmt ∈ (ConstantFunctions.constantFunction model m sig).body,
      StatementAdmits (fun e => acceptedC e = true) stmt := by
  show ∀ stmt ∈ (ConstantFunctions.constantDispatch model m sig).body,
      StatementAdmits (fun e => acceptedC e = true) stmt
  unfold ConstantFunctions.constantDispatch
  split
  all_goals first
    | (intro stmt member
       exact statementAdmits_mono (fun e h => accepted_acceptedC e h) stmt
        (CallPolicy.body_policy model sig stmt member))
    | cadmit

/-- Every tensor adapter function obeys the tensor call inventory: its complete
body admits only tensor-accepted callees. The tensor helper prefix reuses the
scalar helpers (`fail`, the two static-factory helpers), whose scalar admission
widens to the tensor boundary; every dispatched function body is `body_admits`. -/
theorem funcs_acceptedC (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature) :
    ∀ fn ∈ ConstantFunctions.functions model m sigs, checkFunction acceptedC fn = true := by
  intro fn member
  rcases List.mem_append.mp member with helper | exported
  · exact checkFunction_mono (fun e h => accepted_acceptedC e h) fn
      (CallPolicy.helpers_policy fn (ConstantFunctions.helpers_subset fn helper))
  · obtain ⟨sig, _, rfl⟩ := List.mem_map.mp exported
    exact (checkFunction_correct acceptedC _).mpr (body_admits model m sig)

/-! ### The constant no-heap boundary set -/

/-- The named external boundary set of the constant FMI adapter call graph: the same
generated helper/definition names and non-allocating C library / math / atomic
externals and importer logger callback the scalar adapter names, the scalar numerical
kernel entries carried by the reused bodies, together with the three prepared constant
kernel entries `rumoca_constant_rhs`/`rumoca_constant_step`/`rumoca_constant_sample`
the constant derivative getter and step call directly. There are no header-declared
FMI callees: the adapter's public functions do not call one another. -/
def bConstant : CCallPolicy.Externals where
  generated := ["fail", "model_rhs", "model_advance",
    "rumoca_valid_identity", "rumoca_reserve_slot"]
  kernel := ["rumoca_rhs", "rumoca_step", "rumoca_sample",
    "rumoca_constant_rhs", "rumoca_constant_step", "rumoca_constant_sample"]
  header := []
  library := ["isfinite", "floor", "fegetround", "strlen", "strspn", "strcmp",
    "atomic_exchange", "atomic_store"]
  callback := ["logMessage"]

/-- Every constant-accepted callee is admitted by the no-heap boundary set and is
never an allocation entry point. The scalar-accepted callees land in the shared
external roles; the three constant kernel entries land in the kernel role. -/
theorem acceptedC_noHeap (funcs : List Function) (callee : Expr) (acc : acceptedC callee = true) :
    NoHeapCallee funcs bConstant callee = true := by
  cases callee with
  | id name =>
      simp only [acceptedC] at acc
      simp only [NoHeapCallee]
      rcases (Bool.or_eq_true _ _).mp acc with acc3 | sample
      rcases (Bool.or_eq_true _ _).mp acc3 with acc2 | step
      rcases (Bool.or_eq_true _ _).mp acc2 with sc | rhs
      · simp only [accepted, classify] at sc
        split at sc
        · rename_i generated
          simp only [List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at generated
          rcases generated with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals refine (Bool.and_eq_true _ _).mpr ⟨(Bool.or_eq_true _ _).mpr (Or.inr ?_), ?_⟩
          all_goals decide +kernel
        · split at sc
          · rename_i library
            simp only [List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at library
            rcases library with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
            all_goals refine (Bool.and_eq_true _ _).mpr ⟨(Bool.or_eq_true _ _).mpr (Or.inr ?_), ?_⟩
            all_goals decide +kernel
          · split at sc
            · rename_i callback
              subst callback
              refine (Bool.and_eq_true _ _).mpr ⟨(Bool.or_eq_true _ _).mpr (Or.inr ?_), ?_⟩
              all_goals decide +kernel
            · simp at sc
      · rw [beq_iff_eq] at rhs
        subst rhs
        refine (Bool.and_eq_true _ _).mpr ⟨(Bool.or_eq_true _ _).mpr (Or.inr ?_), ?_⟩
        all_goals decide +kernel
      · rw [beq_iff_eq] at step
        subst step
        refine (Bool.and_eq_true _ _).mpr ⟨(Bool.or_eq_true _ _).mpr (Or.inr ?_), ?_⟩
        all_goals decide +kernel
      · rw [beq_iff_eq] at sample
        subst sample
        refine (Bool.and_eq_true _ _).mpr ⟨(Bool.or_eq_true _ _).mpr (Or.inr ?_), ?_⟩
        all_goals decide +kernel
  | _ => rfl

/-- The complete constant adapter function list obeys the no-heap policy: no generated
call graph reaches an allocation entry point, and every callee is a defined
function, a declared kernel entry or a named external. Universal in the state count,
the scalar witness model and the header signature list. -/
theorem constant_no_heap (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature) :
    NoHeap (ConstantFunctions.functions model m sigs) bConstant = true := by
  simp only [NoHeap, List.all_eq_true]
  intro fn member
  exact checkFunction_mono (fun e h => acceptedC_noHeap _ e h) fn
    (funcs_acceptedC model m sigs fn member)

/-! ### The constant acyclic call-graph policy -/

/-- Every constant-accepted callee decreases the shared public-function rank: the
scalar-accepted callees by `classified_rank`, the three constant kernel entries
because they are unranked (numerical-kernel leaves). -/
theorem classifiedC_rank (callee : Expr) (allowed : acceptedC callee = true) :
    rankCallee functionRank 2 callee = true := by
  cases callee with
  | id name =>
      simp only [acceptedC] at allowed
      rcases (Bool.or_eq_true _ _).mp allowed with acc3 | sample
      rcases (Bool.or_eq_true _ _).mp acc3 with acc2 | step
      rcases (Bool.or_eq_true _ _).mp acc2 with sc | rhs
      · exact CallPolicy.classified_rank (.id name) sc
      · rw [beq_iff_eq] at rhs; subst rhs; decide +kernel
      · rw [beq_iff_eq] at step; subst step; decide +kernel
      · rw [beq_iff_eq] at sample; subst sample; decide +kernel
  | _ => rfl

/-- Every dispatched tensor body decreases the public rank along every call. -/
theorem body_rankC (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sig : Signature) :
    ∀ stmt ∈ (ConstantFunctions.constantFunction model m sig).body,
      StatementAdmits (fun e => rankCallee functionRank 2 e = true) stmt := by
  intro stmt member
  apply (statement_calls_complete _ _).mp
  intro callee occurs
  exact classifiedC_rank callee ((statement_calls_complete _ _).mpr
    (body_admits model m sig stmt member) callee occurs)

/-- The complete tensor adapter direct-call graph passes the decidable rank check:
the two numerical kernel entries are unranked leaves, the reused helpers precede
them, and the public functions precede the helpers. -/
theorem functions_rankC (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature) (exports : ∀ sig ∈ sigs, functionRank sig.name = some 2) :
    checkRanks functionRank (ConstantFunctions.functions model m sigs) = true := by
  simp only [checkRanks, List.all_eq_true]
  intro fn member
  rcases List.mem_append.mp member with helper | exported
  · exact (List.all_eq_true.mp CallPolicy.helpers_rank) fn (ConstantFunctions.helpers_subset fn helper)
  · obtain ⟨sig, sigMember, rfl⟩ := List.mem_map.mp exported
    have permitted := (checkFunction_correct (rankCallee functionRank 2)
      (ConstantFunctions.constantFunction model m sig)).mpr (body_rankC model m sig)
    simpa only [checkRank, ConstantFunctions.constantFunction_name, exports sig sigMember] using permitted

/-- Every tensor adapter function name carries a rank: the two kernel entries are
unranked leaves not in the list; the reused helpers rank at 1 and the public
functions at 2. -/
theorem functions_isSomeC (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature) (covered : PublicAPI.Covered sigs) :
    ∀ fn ∈ ConstantFunctions.functions model m sigs, (functionRank fn.signature.name).isSome = true := by
  intro fn member
  rcases List.mem_append.mp member with helper | exported
  · simp only [ConstantFunctions.helpers, TensorFunctions.helpers, List.mem_cons,
      List.not_mem_nil, or_false] at helper
    rcases helper with rfl | rfl | rfl
    all_goals decide +kernel
  · obtain ⟨sig, sigMember, rfl⟩ := List.mem_map.mp exported
    rw [ConstantFunctions.constantFunction_name, CallPolicy.covered_ranks covered sig sigMember]
    rfl

/-- The complete tensor adapter direct-call graph is acyclic: the numerical kernel
entries are unranked leaves, the reused helpers precede them and the public
functions precede the helpers, so no call cycle exists. Universal in the shape, the
scalar witness model and the header signature list. -/
theorem constant_acyclic (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature) (covered : PublicAPI.Covered sigs) :
    Acyclic (ConstantFunctions.functions model m sigs) :=
  acyclic_of_ranked (rank := functionRank)
    ((check_ranks_correct _ _).mp (functions_rankC model m sigs (CallPolicy.covered_ranks covered)))
    (functions_isSomeC model m sigs covered)

end Rumoca.FMI3.ConstantCallPolicy
