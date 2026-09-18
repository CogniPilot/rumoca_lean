import RumocaFMI3.CallPolicy
import RumocaFMI3.TensorFunctions

/-! Classify and bound every call in the tensor FMI adapter function list against
a named boundary set, and instantiate the reusable no-heap and acyclic call-graph
policy. The tensor bodies dispatch the same runtime combinators the scalar adapter
uses, call the shared release/factory helpers, and call the two prepared numerical
kernel entries `rumoca_rhs` and `rumoca_square_jacobian_diag` directly; no generated
call graph names an allocation entry point. Foreign/native and function-pointer
boundaries remain explicit, as for the scalar adapter. -/
namespace Rumoca.FMI3.TensorCallPolicy
open CTree CCalls CCallPolicy
open Rumoca.FMI3.CallPolicy (accepted classify bUnit functionRank)
open Rumoca.Tensor (Shape)
set_option autoImplicit false
variable {source : AST.Model} {shape : Shape}

/-- The tensor adapter admits every callee the scalar classification admits, plus
the second prepared kernel entry `rumoca_square_jacobian_diag`, which the tensor
derivative getter and step call directly. -/
def acceptedT : Expr → Bool
  | .id name => accepted (.id name) || name == "rumoca_square_jacobian_diag"
  | e => accepted e

/-- Every scalar-accepted callee is tensor-accepted. -/
theorem accepted_acceptedT (e : Expr) (acc : accepted e = true) : acceptedT e = true := by
  cases e <;> simp_all [acceptedT]

/-- Monotonicity of the syntactic admission predicate along the call inventory. -/
theorem statementAdmits_mono {p q : Expr → Prop} (imp : ∀ e, p e → q e) (stmt : Stmt)
    (h : StatementAdmits p stmt) : StatementAdmits q stmt :=
  (statement_calls_complete q stmt).mp
    (fun callee mem => imp callee ((statement_calls_complete p stmt).mpr h callee mem))

macro "tadmit" : tactic => `(tactic| (
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
    TensorInstance.timeName, TensorInstance.stateName, TensorInstance.inputName,
    TensorInstance.derivativeName, TensorInstance.outputName]
  fmi_literal_calls
  all_goals simp [StatementAdmits, ExpressionAdmits, acceptedT, accepted, classify,
    Runtime.finite, Runtime.invalidTime, Runtime.allowedExpression, permittedModes,
    Runtime.any, Runtime.all, Runtime.eqv, Runtime.nev, Runtime.both, Runtime.either,
    Runtime.lt, Runtime.le, Runtime.gt, Runtime.ge, Runtime.negate, Runtime.region, Runtime.x,
    Runtime.field, Runtime.setMode, Runtime.mode, Runtime.v, Runtime.n, Runtime.call, Runtime.out,
    Runtime.put, Runtime.pointerCheck, Runtime.scalarAccessCheck, Runtime.countLoop,
    CLoops.loop, CLoops.counterStep]
  done))

set_option maxHeartbeats 4000000 in
/-- Every tensor adapter function body admits only tensor-accepted callees. The 19
genuinely tensor bodies dispatch the runtime combinators and the two prepared kernel
entries; every other signature reuses the scalar body, whose admission is the scalar
`body_policy` widened to the tensor boundary. -/
theorem body_admits (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sig : Signature) :
    ∀ stmt ∈ (TensorFunctions.tensorFunction model m sig).body,
      StatementAdmits (fun e => acceptedT e = true) stmt := by
  show ∀ stmt ∈ (TensorFunctions.tensorDispatch model m sig).body,
      StatementAdmits (fun e => acceptedT e = true) stmt
  unfold TensorFunctions.tensorDispatch
  split
  all_goals first
    | (intro stmt member
       exact statementAdmits_mono (fun e h => accepted_acceptedT e h) stmt
        (CallPolicy.body_policy model sig stmt member))
    | tadmit
    | (cases hout : m.hasOutput <;> tadmit)
    | (cases hos : TensorFunctions.outputShape m <;> tadmit)

/-- Every tensor adapter function obeys the tensor call inventory: its complete
body admits only tensor-accepted callees. The tensor helper prefix reuses the
scalar helpers (`fail`, the two static-factory helpers), whose scalar admission
widens to the tensor boundary; every dispatched function body is `body_admits`. -/
theorem funcs_acceptedT (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List Signature) :
    ∀ fn ∈ TensorFunctions.functions model m sigs, checkFunction acceptedT fn = true := by
  intro fn member
  rcases List.mem_append.mp member with helper | exported
  · exact checkFunction_mono (fun e h => accepted_acceptedT e h) fn
      (CallPolicy.helpers_policy fn (TensorFunctions.helpers_subset fn helper))
  · obtain ⟨sig, _, rfl⟩ := List.mem_map.mp exported
    exact (checkFunction_correct acceptedT _).mpr (body_admits model m sig)

/-! ### The tensor no-heap boundary set -/

/-- The named external boundary set of the tensor FMI adapter call graph: the same
generated helper/definition names and non-allocating C library / math / atomic
externals and importer logger callback the scalar adapter names, together with the
two prepared numerical kernel entries `rumoca_rhs` and `rumoca_square_jacobian_diag`
the tensor derivative getter and step call directly. There are no header-declared
FMI callees: the adapter's public functions do not call one another. -/
def bTensor : CCallPolicy.Externals where
  generated := ["fail", "model_rhs", "model_advance",
    "rumoca_valid_identity", "rumoca_reserve_slot"]
  kernel := ["rumoca_rhs", "rumoca_square_jacobian_diag", "rumoca_step", "rumoca_sample"]
  header := []
  library := ["isfinite", "floor", "fegetround", "strlen", "strspn", "strcmp",
    "atomic_exchange", "atomic_store"]
  callback := ["logMessage"]

/-- Every tensor-accepted callee is admitted by the no-heap boundary set and is
never an allocation entry point. The scalar-accepted callees land in the shared
external roles; the second kernel entry lands in the kernel role. -/
theorem acceptedT_noHeap (funcs : List Function) (callee : Expr) (acc : acceptedT callee = true) :
    NoHeapCallee funcs bTensor callee = true := by
  cases callee with
  | id name =>
      simp only [acceptedT] at acc
      simp only [NoHeapCallee]
      rcases (Bool.or_eq_true _ _).mp acc with sc | jac
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
      · rw [beq_iff_eq] at jac
        subst jac
        refine (Bool.and_eq_true _ _).mpr ⟨(Bool.or_eq_true _ _).mpr (Or.inr ?_), ?_⟩
        all_goals decide +kernel
  | _ => rfl

/-- The complete tensor adapter function list obeys the no-heap policy: no generated
call graph reaches an allocation entry point, and every callee is a defined
function, a declared kernel entry or a named external. Universal in the shape, the
scalar witness model and the header signature list. -/
theorem tensor_no_heap (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List Signature) :
    NoHeap (TensorFunctions.functions model m sigs) bTensor = true := by
  simp only [NoHeap, List.all_eq_true]
  intro fn member
  exact checkFunction_mono (fun e h => acceptedT_noHeap _ e h) fn
    (funcs_acceptedT model m sigs fn member)

/-! ### The tensor acyclic call-graph policy -/

/-- Every tensor-accepted callee decreases the shared public-function rank: the
scalar-accepted callees by `classified_rank`, the second kernel entry because it
is unranked (a numerical-kernel leaf). -/
theorem classifiedT_rank (callee : Expr) (allowed : acceptedT callee = true) :
    rankCallee functionRank 2 callee = true := by
  cases callee with
  | id name =>
      simp only [acceptedT] at allowed
      rcases (Bool.or_eq_true _ _).mp allowed with sc | jac
      · exact CallPolicy.classified_rank (.id name) sc
      · rw [beq_iff_eq] at jac; subst jac; decide +kernel
  | _ => rfl

/-- Every dispatched tensor body decreases the public rank along every call. -/
theorem body_rankT (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sig : Signature) :
    ∀ stmt ∈ (TensorFunctions.tensorFunction model m sig).body,
      StatementAdmits (fun e => rankCallee functionRank 2 e = true) stmt := by
  intro stmt member
  apply (statement_calls_complete _ _).mp
  intro callee occurs
  exact classifiedT_rank callee ((statement_calls_complete _ _).mpr
    (body_admits model m sig stmt member) callee occurs)

/-- The complete tensor adapter direct-call graph passes the decidable rank check:
the two numerical kernel entries are unranked leaves, the reused helpers precede
them, and the public functions precede the helpers. -/
theorem functions_rankT (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List Signature) (exports : ∀ sig ∈ sigs, functionRank sig.name = some 2) :
    checkRanks functionRank (TensorFunctions.functions model m sigs) = true := by
  simp only [checkRanks, List.all_eq_true]
  intro fn member
  rcases List.mem_append.mp member with helper | exported
  · exact (List.all_eq_true.mp CallPolicy.helpers_rank) fn (TensorFunctions.helpers_subset fn helper)
  · obtain ⟨sig, sigMember, rfl⟩ := List.mem_map.mp exported
    have permitted := (checkFunction_correct (rankCallee functionRank 2)
      (TensorFunctions.tensorFunction model m sig)).mpr (body_rankT model m sig)
    simpa only [checkRank, TensorFunctions.tensorFunction_name, exports sig sigMember] using permitted

/-- Every tensor adapter function name carries a rank: the two kernel entries are
unranked leaves not in the list; the reused helpers rank at 1 and the public
functions at 2. -/
theorem functions_isSomeT (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List Signature) (covered : PublicAPI.Covered sigs) :
    ∀ fn ∈ TensorFunctions.functions model m sigs, (functionRank fn.signature.name).isSome = true := by
  intro fn member
  rcases List.mem_append.mp member with helper | exported
  · simp only [TensorFunctions.helpers, List.mem_cons, List.not_mem_nil, or_false] at helper
    rcases helper with rfl | rfl | rfl
    all_goals decide +kernel
  · obtain ⟨sig, sigMember, rfl⟩ := List.mem_map.mp exported
    rw [TensorFunctions.tensorFunction_name, CallPolicy.covered_ranks covered sig sigMember]
    rfl

/-- The complete tensor adapter direct-call graph is acyclic: the numerical kernel
entries are unranked leaves, the reused helpers precede them and the public
functions precede the helpers, so no call cycle exists. Universal in the shape, the
scalar witness model and the header signature list. -/
theorem tensor_acyclic (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List Signature) (covered : PublicAPI.Covered sigs) :
    Acyclic (TensorFunctions.functions model m sigs) :=
  acyclic_of_ranked (rank := functionRank)
    ((check_ranks_correct _ _).mp (functions_rankT model m sigs (CallPolicy.covered_ranks covered)))
    (functions_isSomeT model m sigs covered)

end Rumoca.FMI3.TensorCallPolicy
