import RumocaC.CallPolicyProofs
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

end Rumoca.FMI3.CallPolicy
