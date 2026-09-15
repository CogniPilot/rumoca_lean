import RumocaFMI3.AbsentVariableContract

/-! Raw accessor requests for lifecycle composition. Condition classifies the
count branch of the existing body; it is not the standard's legal importer
issuance relation. Pointer and CS getter/setter ordering remain separate. -/
namespace Rumoca.FMI3.AbsentVariables
open CMemory

inductive Request where
  | empty (ty : VariableType) (write : Bool) (references sizes values : Option Address)
  | reject (ty : VariableType) (write : Bool) (references sizes values : Option Address)
      (n m : UInt64)

def Request.call (request : Request) (p : Address) : String × List Value :=
  match request with
  | .empty ty write references sizes values =>
      ((signature ty write).name, arguments ty.hasSizes (some p) references sizes values 0 0)
  | .reject ty write references sizes values n m =>
      ((signature ty write).name, arguments ty.hasSizes (some p) references sizes values n m)

def Request.Condition : Request → Prop
  | .empty _ _ _ _ _ => True
  | .reject _ _ _ _ _ n m => n.toNat ≠ 0 ∨ m.toNat ≠ 0

def Request.failed : Request → Bool
  | .empty _ _ _ _ _ => false
  | .reject _ _ _ _ _ _ _ => true

def classify (ty : VariableType) (write : Bool) (references sizes values : Option Address)
    (n m : UInt64) : Request :=
  if n.toNat = 0 ∧ m.toNat = 0 then .empty ty write references sizes values
  else .reject ty write references sizes values n m

theorem classify_correct (ty : VariableType) (write : Bool)
    (references sizes values : Option Address) (n m : UInt64) :
    (classify ty write references sizes values n m).Condition := by
  unfold classify
  split
  · trivial
  · rename_i rejected
    exact not_and_or.mp rejected

/-- Classification preserves every raw pointer/count argument in the actual
public call. It does not assume the returned status or callback outcome. -/
theorem classify_call (ty : VariableType) (write : Bool)
    (references sizes values : Option Address) (n m : UInt64) (p : Address) :
    (classify ty write references sizes values n m).call p =
      ((signature ty write).name, arguments ty.hasSizes (some p) references sizes values n m) := by
  unfold classify
  split
  · rename_i empty
    have hn : n = 0 := UInt64.toNat_inj.mp empty.1
    have hm : m = 0 := UInt64.toNat_inj.mp empty.2
    subst n; subst m
    rfl
  · rfl

theorem request_coverage (ty : VariableType) (write : Bool)
    (references sizes values : Option Address) (n m : UInt64) (p : Address) :
    ∃ request : Request, request.Condition ∧ request.call p =
      ((signature ty write).name, arguments ty.hasSizes (some p) references sizes values n m) :=
  ⟨classify ty write references sizes values n m,
    classify_correct ty write references sizes values n m,
    classify_call ty write references sizes values n m p⟩

end Rumoca.FMI3.AbsentVariables
