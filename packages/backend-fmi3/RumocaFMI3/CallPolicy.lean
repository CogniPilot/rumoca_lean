import RumocaC.NoHeapPolicy
import RumocaFMI3.LiteralPreparation
import RumocaFMI3.PublicAPI

/-! Classify and rank calls in every emitted FMI function. Numerical definitions are leaves; foreign/native boundaries remain explicit. -/
namespace Rumoca.FMI3.CallPolicy
open CTree CCalls CCallPolicy

/-- Symbol roles, not an allocation guarantee for foreign implementations. -/
inductive Role where | generated | library | importer

def classify : Expr → Option Role
  | .id name =>
      if ["fail", "model_rhs", "model_advance", "rumoca_rhs", "rumoca_sample",
          "rumoca_valid_identity", "rumoca_reserve_slot"].contains name then some .generated
      else if ["isfinite", "floor", "fegetround", "strlen", "strspn", "strcmp",
          "atomic_exchange", "atomic_store"].contains name then some .library
      else if name = "logMessage" then some .importer else none
  | .field (.id "m") "logger" true => some .importer
  | _ => none

def accepted (callee : Expr) : Bool := (classify callee).isSome

macro "check_fmi_call_policy" : tactic => `(tactic| (
  fmi_literal_calls
  all_goals simp [StatementAdmits, ExpressionAdmits, accepted, classify,
    Runtime.finite, Runtime.invalidTime, Runtime.allowedExpression, permittedModes,
    Runtime.any, Runtime.eqv, Runtime.nev, Runtime.both, Runtime.either,
    Runtime.lt, Runtime.le, Runtime.gt, Runtime.ge, Runtime.negate,
    Runtime.field, Runtime.mode, Runtime.v, Runtime.n, Runtime.call]))

theorem body_policy (model : Solve.FMI3Model source) (sig : Signature) :
    ∀ stmt ∈ Runtime.body model sig, StatementAdmits (fun e => accepted e = true) stmt := by
  unfold Runtime.body
  split <;> check_fmi_call_policy
  all_goals split <;> check_fmi_call_policy
  all_goals by_cases writes : sig.name.startsWith "fmi3Set" = true <;> simp [writes, ExpressionAdmits]

theorem helpers_policy :
    ∀ fn ∈ Runtime.helpers, checkFunction accepted fn = true := by
  intro fn member
  simp [Runtime.helpers] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals apply (checkFunction_correct accepted _).mpr
  all_goals check_fmi_call_policy

theorem functions_policy (model : Solve.FMI3Model source) (sigs : List Signature) :
    ∀ fn ∈ LiteralPreparation.functions model sigs, checkFunction accepted fn = true := by
  intro fn member
  rcases List.mem_append.mp member with helper | exported
  · exact helpers_policy fn helper
  · obtain ⟨sig, _, rfl⟩ := List.mem_map.mp exported
    exact (checkFunction_correct accepted _).mpr (body_policy model sig)

/-- Numerical entry points are leaves; helpers precede them, and public FMI
functions precede helpers. Foreign implementations have no assigned rank. -/
def functionRank (name : String) : Option Nat :=
  if ["rumoca_rhs", "rumoca_step", "rumoca_sample"].contains name then some 0
  else if ["fail", "model_rhs", "model_advance", "rumoca_valid_identity",
      "rumoca_reserve_slot"].contains name then some 1
  else if name.startsWith "fmi3" then some 2 else none

/-- Reuse call classification when checking public function ranks: both
policies inspect the same complete call inventory. -/
theorem classified_rank (callee : Expr) (allowed : accepted callee = true) :
    rankCallee functionRank 2 callee = true := by
  cases callee with
  | id name =>
      simp only [accepted, classify] at allowed
      split at allowed
      · rename_i generated
        simp only [List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at generated
        rcases generated with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals decide +kernel
      · split at allowed
        · rename_i library
          simp only [List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at library
          rcases library with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals decide +kernel
        · split at allowed
          · rename_i callback
            subst name
            decide +kernel
          · simp at allowed
  | _ => rfl

macro "check_fmi_call_rank" : tactic => `(tactic| (
  try fmi_literal_calls
  all_goals try simp [StatementAdmits, ExpressionAdmits, rankCallee, functionRank,
    Runtime.finite, Runtime.invalidTime, Runtime.allowedExpression, permittedModes,
    Runtime.any, Runtime.eqv, Runtime.nev, Runtime.both, Runtime.either,
    Runtime.lt, Runtime.le, Runtime.gt, Runtime.ge, Runtime.negate,
    Runtime.field, Runtime.mode, Runtime.v, Runtime.n, Runtime.call]
  all_goals try decide +kernel))

theorem body_rank (model : Solve.FMI3Model source) (sig : Signature) :
    ∀ stmt ∈ Runtime.body model sig,
      StatementAdmits (fun e => rankCallee functionRank 2 e = true) stmt := by
  intro stmt member
  apply (statement_calls_complete _ _).mp
  intro callee occurs
  exact classified_rank callee ((statement_calls_complete _ _).mpr
    (body_policy model sig stmt member) callee occurs)

theorem helpers_rank : checkRanks functionRank Runtime.helpers = true := by
  simp only [checkRanks, List.all_eq_true]
  intro fn member
  simp [Runtime.helpers] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals change checkFunction (rankCallee functionRank 1) _ = true
  all_goals apply (checkFunction_correct _ _).mpr
  all_goals check_fmi_call_rank

theorem functions_rank (model : Solve.FMI3Model source) (sigs : List Signature)
    (exports : ∀ sig ∈ sigs, functionRank sig.name = some 2) :
    checkRanks functionRank (LiteralPreparation.functions model sigs) = true := by
  simp only [checkRanks, List.all_eq_true]
  intro fn member
  rcases List.mem_append.mp member with helper | exported
  · exact (List.all_eq_true.mp helpers_rank) fn helper
  · obtain ⟨sig, sigMember, rfl⟩ := List.mem_map.mp exported
    have permitted := (checkFunction_correct (rankCallee functionRank 2)
      (Runtime.function model sig)).mpr (body_rank model sig)
    simpa only [checkRank, Runtime.function, exports sig sigMember] using permitted

theorem entry_rank (api : PublicAPI.Entry) : functionRank api.signature.name = some 2 := by
  cases api with
  | factory kind => cases kind <;> decide +kernel
  | initialization enter => cases enter <;> decide +kernel
  | counts events => cases events <;> decide +kernel
  | states write => cases write <;> decide +kernel
  | float64 write => cases write <;> decide +kernel
  | entry which => cases which <;> decide +kernel
  | absent ty write => cases ty <;> cases write <;> decide +kernel
  | capability sig member =>
      have all : ∀ sig ∈ CapabilityRejection.signatures, functionRank sig.name = some 2 := by
        simp only [CapabilityRejection.signatures, List.forall_mem_cons]
        decide +kernel
      exact all sig member
  | _ => decide +kernel

/-- The mandatory header coverage witness supplies the export-rank condition;
it is not left as a new caller assumption. -/
theorem covered_ranks (covered : PublicAPI.Covered sigs) :
    ∀ sig ∈ sigs, functionRank sig.name = some 2 := by
  intro sig member
  obtain ⟨api, rfl⟩ := covered sig member
  exact entry_rank api

/-- The existing preparation table preserves the name of every selected
rendered definition. A duplicate-name exclusion is unnecessary for this fact. -/
theorem program_tree_name (model : Solve.FMI3Model source) (sigs : List Signature)
    (found : (LiteralPreparation.program model sigs).definitions name = some (.tree fn)) :
    fn.signature.name = name := by
  unfold LiteralPreparation.program at found
  cases selected : (LiteralPreparation.functions model sigs).find?
      (fun fn => fn.signature.name == name) with
  | none =>
      simp only [selected] at found
      split at found <;> simp at found
  | some tree =>
      simp only [selected, Option.some.injEq, Definition.tree.injEq] at found
      subst tree
      simpa only [beq_iff_eq] using List.find?_some selected

theorem program_rank (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) :
    ProgramRanked functionRank (LiteralPreparation.program model sigs) := by
  intro name definition found
  cases definition with
  | tree fn =>
      have member := LiteralPreparation.program_covered model sigs name fn found
      obtain ⟨caller, rankName, lowers⟩ :=
        (check_ranks_correct _ _).mp (functions_rank model sigs (covered_ranks covered)) fn member
      rw [program_tree_name model sigs found] at rankName
      exact ⟨caller, rankName, lowers⟩
  | kernel which =>
      unfold LiteralPreparation.program at found
      cases selected : (LiteralPreparation.functions model sigs).find?
          (fun fn => fn.signature.name == name) with
      | some tree => simp [selected] at found
      | none =>
          simp only [selected] at found
          split at found
          all_goals first
            | (refine ⟨0, rfl, ?_⟩; simp [definitionCalls])
            | simp at found

theorem complete_program_no_cycle (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs)
    (first : ProgramEdge (LiteralPreparation.program model sigs) caller callee) :
    ¬ Transition.Reaches (ProgramEdge (LiteralPreparation.program model sigs)) callee caller :=
  program_no_cycle (program_rank model sigs covered) first

/-! ### No-heap and acyclic policy over the scalar adapter function list -/

/-- The named external boundary set of the scalar FMI adapter call graph: the
generated helper/definition names, the declared numerical kernel entries, the
non-allocating C library / math / atomic externals and the importer logger
callback. There are no header-declared FMI callees: the adapter's public
functions do not call one another. The logger callback is also reached through
the instance record function pointer, an indirect callee the policy leaves to
the separate function-pointer boundary. -/
def bUnit : CCallPolicy.Externals where
  generated := ["fail", "model_rhs", "model_advance",
    "rumoca_valid_identity", "rumoca_reserve_slot"]
  kernel := ["rumoca_rhs", "rumoca_step", "rumoca_sample"]
  header := []
  library := ["isfinite", "floor", "fegetround", "strlen", "strspn", "strcmp",
    "atomic_exchange", "atomic_store"]
  callback := ["logMessage"]

/-- Every callee the scalar classification admits is admitted by the no-heap
boundary set and is never an allocation entry point. Both policies inspect the
same complete call inventory. -/
theorem accepted_noHeap (funcs : List Function) (callee : Expr) (acc : accepted callee = true) :
    NoHeapCallee funcs bUnit callee = true := by
  cases callee with
  | id name =>
      simp only [accepted, classify] at acc
      simp only [NoHeapCallee]
      split at acc
      · rename_i generated
        simp only [List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at generated
        rcases generated with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals refine (Bool.and_eq_true _ _).mpr ⟨(Bool.or_eq_true _ _).mpr (Or.inr ?_), ?_⟩
        all_goals decide +kernel
      · split at acc
        · rename_i library
          simp only [List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at library
          rcases library with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals refine (Bool.and_eq_true _ _).mpr ⟨(Bool.or_eq_true _ _).mpr (Or.inr ?_), ?_⟩
          all_goals decide +kernel
        · split at acc
          · rename_i callback
            subst callback
            refine (Bool.and_eq_true _ _).mpr ⟨(Bool.or_eq_true _ _).mpr (Or.inr ?_), ?_⟩
            all_goals decide +kernel
          · simp at acc
  | _ => rfl

/-- The complete scalar adapter function list obeys the no-heap policy: no
generated call graph reaches an allocation entry point, and every callee is a
defined function, a declared kernel entry or a named external. -/
theorem unit_no_heap (model : Solve.FMI3Model source) (sigs : List Signature) :
    NoHeap (LiteralPreparation.functions model sigs) bUnit = true := by
  simp only [NoHeap, List.all_eq_true]
  intro fn member
  exact checkFunction_mono (fun e h => accepted_noHeap _ e h) fn (functions_policy model sigs fn member)

/-- Every scalar adapter function name carries a rank: the numerical kernel
entries, the generated helpers and the ranked public functions. -/
theorem functions_isSome (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) :
    ∀ fn ∈ LiteralPreparation.functions model sigs, (functionRank fn.signature.name).isSome = true := by
  intro fn member
  rcases List.mem_append.mp member with helper | exported
  · simp only [Runtime.helpers, List.mem_cons, List.not_mem_nil, or_false] at helper
    rcases helper with rfl | rfl | rfl | rfl | rfl
    all_goals decide +kernel
  · obtain ⟨sig, sigMember, rfl⟩ := List.mem_map.mp exported
    show (functionRank sig.name).isSome = true
    rw [covered_ranks covered sig sigMember]
    rfl

/-- The complete scalar adapter direct-call graph is acyclic: the numerical
kernel entries are leaves, the generated helpers precede them and the public
functions precede the helpers, so no call cycle exists. -/
theorem unit_acyclic (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) :
    Acyclic (LiteralPreparation.functions model sigs) :=
  acyclic_of_ranked (rank := functionRank)
    ((check_ranks_correct _ _).mp (functions_rank model sigs (covered_ranks covered)))
    (functions_isSome model sigs covered)

end Rumoca.FMI3.CallPolicy
