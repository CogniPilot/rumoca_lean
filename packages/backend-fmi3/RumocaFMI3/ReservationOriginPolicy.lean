import RumocaFMI3.CallPolicy
import RumocaC.CallSubprogram

namespace Rumoca.FMI3.ReservationOrigin
open CTree CMemory CCalls CCallSites

def factory (name : String) : Prop :=
  name = "fmi3InstantiateModelExchange" ∨ name = "fmi3InstantiateCoSimulation"

/-- The closed domain for an invocation which is not a factory. -/
def allowed (name : String) : Bool :=
  !(["fmi3InstantiateModelExchange", "fmi3InstantiateCoSimulation",
    "rumoca_reserve_slot", "atomic_exchange"].contains name)

def Permitted (operand : Indirect.Operand) : Prop :=
  match operand.callee with
  | .id name => allowed name = true
  | _ => True

theorem excluded (name : String) : allowed name = false ↔
    factory name ∨ name = "rumoca_reserve_slot" ∨ name = "atomic_exchange" := by
  simp [allowed, factory, or_assoc]
  tauto

macro "check_no_reservation" : tactic => `(tactic| (
  try fmi_literal_calls
  all_goals try simp_all [Admits, Indirect.operand, Permitted, allowed]))

set_option maxHeartbeats 1000000 in
theorem body_policy (model : Solve.FMI3Model source) (sig : Signature)
    (selected : allowed sig.name = true) : ∀ stmt ∈ Runtime.body model sig, Admits Permitted stmt := by
  unfold Runtime.body
  split <;> check_no_reservation
  all_goals split <;> check_no_reservation

theorem helpers_policy (fn : Function) (member : fn ∈ Runtime.helpers)
    (selected : allowed fn.signature.name = true) : ∀ stmt ∈ fn.body, Admits Permitted stmt := by
  simp only [Runtime.helpers, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals check_no_reservation
  all_goals simp [CAtomicScan.function] at selected

theorem functions_policy (model : Solve.FMI3Model source) (sigs : List Signature)
    (fn : Function) (member : fn ∈ LiteralPreparation.functions model sigs)
    (selected : allowed fn.signature.name = true) : ∀ stmt ∈ fn.body, Admits Permitted stmt := by
  rcases List.mem_append.mp member with helper | exported
  · exact helpers_policy fn helper selected
  · obtain ⟨sig, _, rfl⟩ := List.mem_map.mp exported
    exact body_policy model sig selected

theorem program_policy (model : Solve.FMI3Model source) (sigs : List Signature)
    (name : String) (selected : allowed name = true) (fn : Function)
    (found : (LiteralPreparation.program model sigs).definitions name = some (.tree fn)) :
    ∀ stmt ∈ fn.body, Admits Permitted stmt := by
  exact functions_policy model sigs fn (LiteralPreparation.program_covered model sigs name fn found)
    (by rw [CallPolicy.program_tree_name model sigs found]; exact selected)

variable [CInterface] {E : Type}

theorem operand_sound (program : Events.Program E)
    (onlyNamed : ∀ name, allowed name = false → NamedOnly program name) :
    OperandSound program Permitted (fun name _ => allowed name = true) := by
  intro operand admitted env heap name values resolved evaluated
  cases selected : allowed name with
  | true => rfl
  | false =>
    have named := CCallPolicy.named_origin env heap operand.callee
      (named_resolution program (onlyNamed name selected) resolved)
    simpa only [Permitted, named, selected] using admitted

theorem event_ready (model : Solve.FMI3Model source) (sigs : List Signature)
    (program : Events.Program E) (actual : program.internal = LiteralPreparation.program model sigs)
    (onlyNamed : ∀ name, allowed name = false → NamedOnly program name)
    (ready : Ready Permitted (fun name _ => allowed name = true) before)
    (step : Events.Step program before events after) : Ready Permitted (fun name _ => allowed name = true) after := by
  exact Subprogram.event_ready program allowed
    (fun name selected fn found => program_policy model sigs name selected fn (actual ▸ found))
    (operand_sound program onlyNamed) ready step

end Rumoca.FMI3.ReservationOrigin
