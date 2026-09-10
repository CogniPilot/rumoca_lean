import RumocaC.BooleanProofs
import RumocaFMI3.CInterface
import RumocaFMI3.GuardProofs

/-! The generated lifecycle guards in the shared C memory/execution model.
This connects the actual guard expression and statement prefix to the
independently authored lifecycle predicate. Instance bindings and represented
kind/mode fields are explicit; printed bytes, ABI validity and logging remain
separate obligations. No additional command or lifecycle state is admitted. -/
namespace Rumoca.FMI3.LifecycleGuard
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses
open CTree CMemory CBody

omit static in
theorem mode_code_beq (a b : Mode) : ((a.code : Int) == (b.code : Int)) = (a == b) := by
  cases a <;> cases b <;> rfl

theorem modes_eval (env : Locals) (heap : Heap) (p : Address) (current : Mode)
    (hm : resolve env "m" = some (.pointer (some p)))
    (hc : load heap (p.member "mode") = some (.integer current.code)) (modes : List Mode) :
    eval env heap (Runtime.any (modes.map fun m =>
      Runtime.eqv (Runtime.field "mode") (Runtime.mode m))) =
      some (boolean (modes.contains current)) := by
  induction modes with
  | nil => rfl
  | cons head tail ih =>
    have hhead : eval env heap (Runtime.eqv (Runtime.field "mode") (Runtime.mode head)) =
        some (boolean (current == head)) := by
      simp [Runtime.eqv, Runtime.field, Runtime.mode, Runtime.v, Runtime.n,
        eval, hm, hc, Value.address, comparison, mode_code_beq]
    simpa [Runtime.any, List.contains_cons] using BoolProofs.eval_or hhead ih

theorem eval_correct (env : Locals) (heap : Heap) (p : Address)
    (cmd : Command) (kind : Kind) (mode : Mode)
    (hp : resolve env "m" = some (.pointer (some p)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code)) :
    eval env heap (Runtime.allowedExpression cmd) = some (boolean (allowed cmd kind mode)) := by
  have hme : eval env heap (Runtime.eqv (Runtime.field "kind") (Runtime.n 0)) =
      some (boolean (kind.code == 0)) := by
    cases kind <;> simp [Runtime.eqv, Runtime.field, Runtime.v, Runtime.n, eval,
      hp, hk, Value.address, comparison, Kind.code, boolean]
  have hcs : eval env heap (Runtime.eqv (Runtime.field "kind") (Runtime.n 1)) =
      some (boolean (kind.code == 1)) := by
    cases kind <;> simp [Runtime.eqv, Runtime.field, Runtime.v, Runtime.n, eval,
      hp, hk, Value.address, comparison, Kind.code, boolean]
  have h := BoolProofs.eval_or
    (BoolProofs.eval_and hme (modes_eval env heap p mode hp hm (permittedModes cmd .me)))
    (BoolProofs.eval_and hcs (modes_eval env heap p mode hp hm (permittedModes cmd .cs)))
  cases kind <;> simpa [Runtime.allowedExpression, Runtime.either, Runtime.both, allowed, Kind.code] using h

theorem reference (env : Locals) (heap : Heap) (p : Address)
    (cmd : Command) (kind : Kind) (mode : Mode)
    (hp : resolve env "m" = some (.pointer (some p)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code)) :
    eval env heap (Runtime.allowedExpression cmd) = some (boolean true) ↔
      Reference.Allowed cmd kind mode := by
  rw [eval_correct env heap p cmd kind mode hp hk hm]
  have hb : ∀ b, boolean b = boolean true ↔ b = true := by intro b; cases b <;> decide
  rw [Option.some.injEq, hb, allowed_correct]

set_option maxRecDepth 10000 in
/-- Execute the whole instance/lifecycle prefix without changing the heap. -/
theorem require_run (env : Locals) (heap : Heap) (p : Address)
    (cmd : Command) (kind : Kind) (mode : Mode) (rest : List Stmt)
    (hi : env "instance" = some (.pointer (some p))) (hn : env "m" = none)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code)) :
    run 3 (.running (Runtime.require cmd ++ rest) env heap) =
      some (.running ((if allowed cmd kind mode then [] else
        [Runtime.fail "Call is not allowed in the current FMI state"]) ++ rest)
        (CBody.bind env "m" (.pointer (some p))) heap) := by
  have hg := eval_correct (CBody.bind env "m" (.pointer (some p))) heap p cmd kind mode
    (by simp [CBody.bind, resolve]) hk hm
  cases ha : allowed cmd kind mode <;>
    simp [Runtime.require, Runtime.instancePrefix, Runtime.reject, Runtime.branch,
      Runtime.ret, Runtime.negate, Runtime.v, run, next, eval, CBody.bind, resolve,
      constants, CBody.cast, convert, boolean, Value.truth, hi, hn, hg, ha]

theorem accept (env : Locals) (heap : Heap) (p : Address)
    (cmd : Command) (kind : Kind) (mode : Mode) (rest : List Stmt)
    (hi : env "instance" = some (.pointer (some p))) (hn : env "m" = none)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (ha : Reference.Allowed cmd kind mode) :
    run 3 (.running (Runtime.require cmd ++ rest) env heap) =
      some (.running rest (CBody.bind env "m" (.pointer (some p))) heap) := by
  simpa only [(allowed_correct cmd kind mode).mpr ha, Bool.true_eq, ↓reduceIte, List.nil_append]
    using require_run env heap p cmd kind mode rest hi hn hk hm

/-- Rejected lifecycle calls reach the emitted failure call. Execution of
that helper, its logger and its final Error status is a separate obligation. -/
theorem reject_prefix (env : Locals) (heap : Heap) (p : Address)
    (cmd : Command) (kind : Kind) (mode : Mode) (rest : List Stmt)
    (hi : env "instance" = some (.pointer (some p))) (hn : env "m" = none)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (ha : ¬ Reference.Allowed cmd kind mode) :
    run 3 (.running (Runtime.require cmd ++ rest) env heap) =
      some (.running (Runtime.fail "Call is not allowed in the current FMI state" :: rest)
        (CBody.bind env "m" (.pointer (some p))) heap) := by
  have hb : allowed cmd kind mode = false :=
    Bool.eq_false_iff.mpr (fun h => ha ((allowed_correct cmd kind mode).mp h))
  simpa only [hb, Bool.false_eq_true, ↓reduceIte, List.singleton_append]
    using require_run env heap p cmd kind mode rest hi hn hk hm

end Rumoca.FMI3.LifecycleGuard
