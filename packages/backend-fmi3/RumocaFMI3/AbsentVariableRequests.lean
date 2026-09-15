import RumocaFMI3.AbsentVariableContract

/-! Total raw access classification by endpoint and then counts. It retains
all caller arguments and represents rejected empty setters explicitly. Legal
importer pointer rules and CS call ordering remain separate obligations. -/
namespace Rumoca.FMI3.AbsentVariables
open CMemory

inductive Request where
  | empty (ty : VariableType) (write : Bool) (references sizes values : Option Address)
  | reject (reason : Failure) (ty : VariableType) (write : Bool)
      (references sizes values : Option Address) (n m : UInt64)

def Request.call (request : Request) (p : Address) : String × List Value :=
  match request with
  | .empty ty write references sizes values =>
      ((signature ty write).name, arguments ty.hasSizes (some p) references sizes values 0 0)
  | .reject _ ty write references sizes values n m =>
      ((signature ty write).name, arguments ty.hasSizes (some p) references sizes values n m)

def Request.Condition (request : Request) (kind : Kind) (mode : Mode) : Prop :=
  match request with
  | .empty _ write _ _ _ => Reference.Allowed (accessCommand write) kind mode
  | .reject reason _ write _ _ _ n m => reason.Condition write kind mode n m

def Request.failed : Request → Bool
  | .empty _ _ _ _ _ => false
  | .reject _ _ _ _ _ _ _ _ => true

def classify (ty : VariableType) (write : Bool) (kind : Kind) (mode : Mode)
    (references sizes values : Option Address) (n m : UInt64) : Request :=
  if allowed (accessCommand write) kind mode then
    if n.toNat = 0 ∧ m.toNat = 0 then .empty ty write references sizes values
    else .reject .selection ty write references sizes values n m
  else .reject .lifecycle ty write references sizes values n m

theorem classify_correct (ty : VariableType) (write : Bool) (kind : Kind) (mode : Mode)
    (references sizes values : Option Address) (n m : UInt64) :
    (classify ty write kind mode references sizes values n m).Condition kind mode := by
  unfold classify
  split
  · rename_i permitted
    have legal := (allowed_correct (accessCommand write) kind mode).mp permitted
    split
    · exact legal
    · rename_i nonempty
      exact ⟨legal, not_and_or.mp nonempty⟩
  · rename_i denied
    exact fun legal => denied ((allowed_correct (accessCommand write) kind mode).mpr legal)

/-- Every raw pointer and cardinality survives classification, including
nonempty requests rejected before any array access. -/
theorem classify_call (ty : VariableType) (write : Bool) (kind : Kind) (mode : Mode)
    (references sizes values : Option Address) (n m : UInt64) (p : Address) :
    (classify ty write kind mode references sizes values n m).call p =
      ((signature ty write).name, arguments ty.hasSizes (some p) references sizes values n m) := by
  unfold classify
  split
  · split
    · rename_i empty
      have hn : n = 0 := UInt64.toNat_inj.mp empty.1
      have hm : m = 0 := UInt64.toNat_inj.mp empty.2
      subst n; subst m
      rfl
    · rfl
  · rfl

/-- Totality over both interfaces, every modeled mode, every absent type,
both access directions, and arbitrary pointer/count arguments. -/
theorem request_coverage (ty : VariableType) (write : Bool) (kind : Kind) (mode : Mode)
    (references sizes values : Option Address) (n m : UInt64) (p : Address) :
    ∃ request : Request, request.Condition kind mode ∧ request.call p =
      ((signature ty write).name, arguments ty.hasSizes (some p) references sizes values n m) :=
  ⟨classify ty write kind mode references sizes values n m,
    classify_correct ty write kind mode references sizes values n m,
    classify_call ty write kind mode references sizes values n m p⟩

theorem terminated_setter (ty : VariableType) (kind : Kind)
    (references sizes values : Option Address) (n m : UInt64) :
    classify ty true kind .terminated references sizes values n m =
      .reject .lifecycle ty true references sizes values n m := by
  simp [classify, accessCommand, variable_setter_terminated]

theorem cs_step_empty (ty : VariableType) (references sizes values : Option Address) :
    classify ty true .cs .step references sizes values 0 0 =
      .empty ty true references sizes values := rfl

end Rumoca.FMI3.AbsentVariables
