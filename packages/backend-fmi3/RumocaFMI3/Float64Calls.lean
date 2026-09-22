import RumocaFMI3.ArrayAccess
import RumocaC.LoopEvents
import RumocaFMI3.GuardedCalls
import RumocaFMI3.DerivativeContract

noncomputable section
namespace Rumoca.FMI3.Float64Calls
open CTree CMemory CBody

def signature (write : Bool) : Signature :=
  ⟨"fmi3Status", if write then "fmi3SetFloat64" else "fmi3GetFloat64",
    [⟨"fmi3Instance", "instance", false⟩, ⟨"const fmi3ValueReference", "valueReferences", true⟩,
     ⟨"size_t", "nValueReferences", false⟩,
     ⟨if write then "const fmi3Float64" else "fmi3Float64", "values", true⟩,
     ⟨"size_t", "nValues", false⟩]⟩

def arguments (handle references values : Option Address) (n m : UInt64) : List Value :=
  [.pointer handle, .pointer references, .integer n.toNat, .pointer values, .integer m.toNat]

def parameters (handle references values : Option Address) (n m : UInt64) : Locals :=
  bind (bind (bind (bind (bind (fun _ => none) "nValues" (.integer m.toNat))
    "values" (.pointer values)) "nValueReferences" (.integer n.toNat))
    "valueReferences" (.pointer references)) "instance" (.pointer handle)

def locals (p : Address) (references values : Option Address) (n m : UInt64) : Locals :=
  bind (parameters (some p) references values n m) "m" (.pointer (some p))

def reference : Expr := .index (Runtime.v "valueReferences") (Runtime.v "k")
def output : Expr := .index (Runtime.v "values") (Runtime.v "k")
def validation : Stmt := Runtime.reject (Runtime.gt reference (Runtime.n 2)) "Unknown value reference"

def readBody : List Stmt := [
  Runtime.branch (Runtime.eqv reference (Runtime.n 0)) [.assign output (Runtime.field "time")]
    [Runtime.branch (Runtime.eqv reference (Runtime.n 1)) [.assign output Runtime.x]
      [.assign output (Runtime.call "model_rhs" [.address (Runtime.field "model")])]]]

def afterValidation : List Stmt := [.assign (Runtime.v "k") (Runtime.n 0),
  CLoops.loop "k" (Runtime.v "nValueReferences") readBody, Runtime.ok]

def afterGuard : List Stmt :=
  CLoops.counted "k" (Runtime.v "nValueReferences") [validation] ++ afterValidation

def getTail : List Stmt := ArrayAccess.float64Guard :: afterGuard

theorem getter_body (model : Solve.FMI3Model source) :
    Runtime.body model (signature false) = Runtime.require .get ++ getTail := rfl

theorem validation_closed : CLoops.noDeclarations validation = true := by
  simp [validation, Runtime.reject, Runtime.branch, Runtime.fail, Runtime.ret, CLoops.noDeclarations]
theorem read_closed : readBody.all CLoops.noDeclarations = true := by
  simp [readBody, Runtime.branch, CLoops.noDeclarations]

section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

theorem parameters_bound (write : Bool) (handle references values : Option Address) (n m : UInt64) :
    CCalls.parameters (signature write).parameters (arguments handle references values n m) =
      some (parameters handle references values n m) := by
  have nc : CBody.cast "size_t" (.integer n.toNat) = some (.integer n.toNat) :=
    CLoops.Calls.cast_of_type "size_t" .size _ _ rfl (CLoops.convert_size_nat _ n.toNat_lt_size)
  have mc : CBody.cast "size_t" (.integer m.toNat) = some (.integer m.toNat) :=
    CLoops.Calls.cast_of_type "size_t" .size _ _ rfl (CLoops.convert_size_nat _ m.toNat_lt_size)
  cases write <;>
    simp only [signature, arguments, CCalls.parameters, CCalls.parameterType, Bool.false_eq_true, ↓reduceIte, nc, mc]
  all_goals rfl

theorem get_guard_run (model : Solve.FMI3Model source) (heap : Heap) (p : Address)
    (references values : Option Address) (n m : UInt64) (kind : Kind) (mode : Mode)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode) :
    run 4 (.running (Runtime.body model (signature false)) (parameters (some p) references values n m) heap) =
      some (.running
        (if ArrayAccess.Valid references values n m then afterGuard else
          Runtime.fail "Invalid Float64 array lengths or pointers" :: afterGuard)
        (locals p references values n m) heap) := by
  have accepted := LifecycleGuard.accept (parameters (some p) references values n m) heap p
    .get kind mode getTail (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind]) hk hm allowed
  rw [getter_body, show 4 = 3 + 1 from rfl, run_add, accepted]
  exact ArrayAccess.run_guard (locals p references values n m) heap "valueReferences" "values"
    "nValueReferences" "nValues" "Invalid Float64 array lengths or pointers" references values n m afterGuard
    (by simp [locals, parameters, CBody.bind, resolve]) (by simp [locals, parameters, CBody.bind, resolve])
    (by simp [locals, parameters, CBody.bind, resolve]) (by simp [locals, parameters, CBody.bind, resolve])

end

section
variable [interface : CInterface]

theorem reference_eval (env : Locals) (heap : Heap) (p : Address) (i : Nat) (value : UInt32)
    (pointer : resolve env "valueReferences" = some (.pointer (some p)))
    (counter : resolve env "k" = some (.integer i))
    (loaded : load heap (p.index i) = some (.integer value.toNat)) :
    eval env heap reference = some (.integer value.toNat) := by
  simp [reference, Runtime.v, CBody.eval, CBody.evalWith, pointer, counter, Value.address, loaded]

theorem validation_step (env : Locals) (types : CLoops.Types) (heap : Heap)
    (rest : List Stmt) (value : UInt32)
    (loaded : eval env heap reference = some (.integer value.toNat)) :
    CLoops.next (.running (validation :: rest) env types heap) =
      some (.running (if value.toNat ≤ 2 then rest else Runtime.fail "Unknown value reference" :: rest)
        env types heap) := by
  by_cases valid : value.toNat ≤ 2
  · have bound : ¬ (value.toNat : Int) > 2 := by omega
    simp [validation, Runtime.reject, Runtime.branch, Runtime.gt, Runtime.n, Runtime.fail, Runtime.ret,
      CLoops.next, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions, CLoops.noDeclarations, CBody.eval, CBody.evalWith, loaded, comparison,
      boolean, Value.truth, valid, bound]
  · have bound : (value.toNat : Int) > 2 := by omega
    simp [validation, Runtime.reject, Runtime.branch, Runtime.gt, Runtime.n, Runtime.fail, Runtime.ret,
      CLoops.next, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions, CLoops.noDeclarations, CBody.eval, CBody.evalWith, loaded, comparison,
      boolean, Value.truth, valid, bound]

end
end Rumoca.FMI3.Float64Calls
