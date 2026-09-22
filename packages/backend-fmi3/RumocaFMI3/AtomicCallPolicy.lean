import RumocaC.CallSites
import RumocaC.AtomicCalls
import RumocaFMI3.CallPolicy

/-! Derive reservation/release values from the generated C operands and ordinary Boolean evaluation. -/
namespace Rumoca.FMI3.AtomicCallPolicy
open CTree CMemory CCalls CCallSites

/-- Reservation sets a flag; release clears it. This restricts the value,
not the address, ownership or the authorization to release a particular slot. -/
def desired (name : String) : Option Bool :=
  if name = "atomic_exchange" then some true
  else if name = "atomic_store" then some false else none

def DesiredValue (busy : Bool) : Expr → Prop
  | .cast type (.nat n) => type = "_Bool" ∧ n = (if busy then 1 else 0)
  | _ => False

instance (busy : Bool) (value : Expr) : Decidable (DesiredValue busy value) := by
  unfold DesiredValue
  split <;> infer_instance

def DesiredArguments (busy : Bool) : List Expr → Prop
  | [_, value] => DesiredValue busy value
  | _ => False

instance (busy : Bool) (args : List Expr) : Decidable (DesiredArguments busy args) := by
  unfold DesiredArguments
  split <;> infer_instance

def Permitted (operand : Indirect.Operand) : Prop :=
  match operand.callee with
  | .id name => match desired name with
    | some busy => DesiredArguments busy operand.args
    | none => True
  | _ => True

instance (operand : Indirect.Operand) : Decidable (Permitted operand) := by
  unfold Permitted
  split
  · split <;> infer_instance
  · infer_instance

def check (operand : Indirect.Operand) : Bool := decide (Permitted operand)

theorem check_correct (operand : Indirect.Operand) : check operand = true ↔ Permitted operand := by
  exact decide_eq_true_iff

/-- The scheduler-operand admission predicate is monotone in the operand
restriction: a weaker per-operand policy is admitted wherever a stronger one is.
This lets a subordinate operand policy instantiate the shared body/helper
classification instead of re-classifying every call site. -/
theorem admits_mono {p q : Indirect.Operand → Prop} (imp : ∀ operand, p operand → q operand)
    (stmt : Stmt) (h : Admits p stmt) : Admits q stmt := by
  revert h
  induction stmt using Stmt.rec
      (motive_2 := fun code => (∀ s ∈ code, Admits p s) → ∀ s ∈ code, Admits q s) with
  | declare | assign | eval | ret =>
      intro hp
      simp only [Admits] at hp ⊢
      exact ⟨fun operand occurs => imp operand (hp.1 operand occurs), trivial⟩
  | branch _ _ _ hy hn =>
      intro hp
      simp only [Admits] at hp ⊢
      exact ⟨fun operand occurs => imp operand (hp.1 operand occurs), hy hp.2.1, hn hp.2.2⟩
  | whileLoop _ _ hb =>
      intro hp
      simp only [Admits] at hp ⊢
      exact ⟨fun operand occurs => imp operand (hp.1 operand occurs), hb hp.2⟩
  | nil => simp_all
  | cons s rest hs hrest =>
      rename_i hall s' member
      rcases List.mem_cons.mp member with rfl | tail
      · exact hs (hall s' List.mem_cons_self)
      · exact hrest (fun x hx => hall x (List.mem_cons_of_mem _ hx)) s' tail

def ValidCall (name : String) (values : List Value) : Prop :=
  ∀ busy, desired name = some busy → ∃ pointer, values = [pointer, CAtomicBoolean.value busy]

variable [interface : CInterface]

theorem boolean_eval (boolean : interface.types "_Bool" = some .boolean)
    (env : CBody.Locals) (heap : Heap) (busy : Bool) :
    CBody.eval env heap (.cast "_Bool" (.nat (if busy then 1 else 0))) =
      some (CAtomicBoolean.value busy) := by
  cases busy <;> simp [CBody.eval, CBody.evalWith, CBody.expressionCast, CBody.cast, CBody.zeroLiteral,
    boolean, convert, Value.truth, CAtomicBoolean.value]

theorem arguments_value (boolean : interface.types "_Bool" = some .boolean)
    (shape : DesiredArguments busy args) (evaluated : arguments env heap args = some values) :
    ∃ pointer, values = [pointer, CAtomicBoolean.value busy] := by
  unfold DesiredArguments at shape
  split at shape
  · rename_i pointer value
    have exactValue : value = .cast "_Bool" (.nat (if busy then 1 else 0)) := by
      unfold DesiredValue at shape
      split at shape
      · obtain ⟨rfl, rfl⟩ := shape
        rfl
      · contradiction
    subst value
    simp only [arguments, argumentsWith, CBody.legacyExpressions, boolean_eval boolean, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def, Option.bind_eq_some_iff] at evaluated
    obtain ⟨pointerValue, _, result⟩ := evaluated
    exact ⟨pointerValue, (Option.some.inj result).symm⟩
  · contradiction

theorem operand_sound (program : Events.Program E)
    (boolean : interface.types "_Bool" = some .boolean)
    (onlyNamed : ∀ name busy, desired name = some busy → NamedOnly program name) :
    OperandSound program Permitted ValidCall := by
  intro operand admitted env heap name values resolved evaluated busy selected
  have origin := CCallPolicy.named_origin env heap operand.callee
    (named_resolution program (onlyNamed name busy selected) resolved)
  have shape : DesiredArguments busy operand.args := by
    simpa only [Permitted, origin, selected] using admitted
  exact arguments_value boolean shape evaluated

end Rumoca.FMI3.AtomicCallPolicy

namespace Rumoca.FMI3.AtomicCallPolicy
open CTree CMemory CCalls CCallSites

macro "check_fmi_atomic_operands" : tactic => `(tactic| (
  try fmi_literal_calls
  all_goals try simp [Admits, Indirect.operand, Permitted, desired, DesiredArguments, DesiredValue]))

set_option maxHeartbeats 1000000 in
theorem body_policy (model : Solve.FMI3Model source) (sig : Signature) :
    ∀ stmt ∈ Runtime.body model sig, Admits Permitted stmt := by
  unfold Runtime.body
  split <;> check_fmi_atomic_operands
  all_goals split <;> check_fmi_atomic_operands

theorem helpers_policy : ∀ fn ∈ Runtime.helpers, ∀ stmt ∈ fn.body, Admits Permitted stmt := by
  intro fn member
  simp only [Runtime.helpers, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals check_fmi_atomic_operands

theorem functions_policy (model : Solve.FMI3Model source) (sigs : List Signature) :
    ∀ fn ∈ LiteralPreparation.functions model sigs, ∀ stmt ∈ fn.body, Admits Permitted stmt := by
  intro fn member
  rcases List.mem_append.mp member with helper | exported
  · exact helpers_policy fn helper
  · obtain ⟨sig, _, rfl⟩ := List.mem_map.mp exported
    exact body_policy model sig

theorem program_policy (model : Solve.FMI3Model source) (sigs : List Signature) :
    ProgramAdmits Permitted (LiteralPreparation.program model sigs) := by
  intro name fn found
  exact functions_policy model sigs fn (LiteralPreparation.program_covered model sigs name fn found)

end Rumoca.FMI3.AtomicCallPolicy
