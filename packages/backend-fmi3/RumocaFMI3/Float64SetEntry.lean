import RumocaFMI3.Float64Contract
import RumocaFMI3.SetterScope
import RumocaC.FiniteValue

/-! Public setter entry through the shared parameter layout, array guard,
scope-hoisting law and generic loop scheduler. The complete setter contract
composes this entry with validation, state writes and failure callbacks. -/
noncomputable section
namespace Rumoca.FMI3.Float64Set
open CTree CMemory CBody CLoops Float64Calls

def message : String := "Only a finite continuous state value may be set"
def validation : Stmt := Runtime.reject (Runtime.either (Runtime.nev reference (Runtime.n 1))
  (Runtime.negate (Runtime.finite output))) message
def writeBody : List Stmt := [.assign Runtime.x output]
def afterValidation : List Stmt := [.assign (Runtime.v "k") (Runtime.n 0),
  loop "k" (Runtime.v "nValueReferences") writeBody, Runtime.ok]
def afterGuard : List Stmt := counted "k" (Runtime.v "nValueReferences") [validation] ++ afterValidation

theorem body_eq (model : Solve.FMI3Model source) :
    Runtime.body model (signature true) = Runtime.setFloat64 := rfl

theorem values_eq : Runtime.setFloat64Values = ArrayAccess.float64Guard :: afterGuard := rfl

theorem validation_closed : noDeclarations validation = true := by
  simp [validation, Runtime.reject, Runtime.branch, Runtime.fail, Runtime.ret, noDeclarations]

theorem write_closed : writeBody.all noDeclarations = true := by
  simp [writeBody, noDeclarations]

section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

theorem entry_run (model : Solve.FMI3Model source) (heap : Heap) (p : Address)
    (input buffer : Option Address) (n m : UInt64) (kind : Kind) (mode : Mode)
    (nonempty : n.toNat ≠ 0 ∨ m.toNat ≠ 0)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code)) :
    CBody.run 4 (.running (Runtime.body model (signature true)) (parameters (some p) input buffer n m) heap) =
      some (.running ((if allowed .setStart kind mode then [] else
        [Runtime.fail ErrorCalls.rejectionMessage]) ++ Runtime.setFloat64Values)
        (locals p input buffer n m) heap) := by
  exact SetterScope.entry_run _ heap p kind mode n.toNat m.toNat
    (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind])
    (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind]) nonempty hk hm

theorem guard_run (model : Solve.FMI3Model source) (heap : Heap) (p : Address)
    (input buffer : Option Address) (n m : UInt64) (kind : Kind) (mode : Mode)
    (nonempty : n.toNat ≠ 0 ∨ m.toNat ≠ 0)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (permitted : Reference.Allowed .setStart kind mode) :
    CBody.run 5 (.running (Runtime.body model (signature true)) (parameters (some p) input buffer n m) heap) =
      some (.running (if ArrayAccess.Valid input buffer n m then afterGuard else
        Runtime.fail "Invalid Float64 array lengths or pointers" :: afterGuard)
        (locals p input buffer n m) heap) := by
  have entered := entry_run model heap p input buffer n m kind mode nonempty hk hm
  rw [(allowed_correct _ _ _).mpr permitted] at entered
  simp only [↓reduceIte, List.nil_append, values_eq] at entered
  rw [show 5 = 4 + 1 from rfl, CBody.run_add, entered]
  exact ArrayAccess.run_guard _ heap "valueReferences" "values" "nValueReferences" "nValues"
    "Invalid Float64 array lengths or pointers" input buffer n m afterGuard
    (by simp [locals, parameters, CBody.bind, resolve]) (by simp [locals, parameters, CBody.bind, resolve])
    (by simp [locals, parameters, CBody.bind, resolve]) (by simp [locals, parameters, CBody.bind, resolve])

theorem empty_behaviors (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (p : Address) (input buffer : Option Address) (kind : Kind) (mode : Mode)
    (defined : program.internal.definitions (signature true).name =
      some (.tree (Runtime.function model (signature true))))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code)) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling (signature true).name (arguments (some p) input buffer 0 0) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, heap⟩ := by
  apply CCalls.Events.body_call_behaviors program (Runtime.function model (signature true))
    (arguments (some p) input buffer 0 0) (parameters (some p) input buffer 0 0) heap
    ⟨.integer 0, heap⟩ (.integer 0) 5 defined (parameters_bound true _ _ _ _ _)
    (BodyEmbedding.body_closed model (signature true))
  · exact SetterScope.hoisted_empty_run _ heap p kind mode Runtime.setFloat64Values
      (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind])
      (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind])
      (by simp [parameters, CBody.bind]) hk hm
  · rfl

theorem null_behaviors (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (input buffer : Option Address) (n m : UInt64)
    (defined : program.internal.definitions (signature true).name =
      some (.tree (Runtime.function model (signature true)))) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling (signature true).name (arguments none input buffer n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  apply GuardedCalls.null_behaviors program (Runtime.function model (signature true))
    ([Runtime.branch SetterScope.empty [Runtime.modeGuard .get, Runtime.ok], Runtime.modeGuard .setStart] ++
      Runtime.setFloat64Values) (arguments none input buffer n m) (parameters none input buffer n m)
    heap defined (parameters_bound true _ _ _ _ _) rfl rfl (BodyEmbedding.body_closed model (signature true))
  all_goals simp [parameters, CBody.bind]

end
end Rumoca.FMI3.Float64Set
