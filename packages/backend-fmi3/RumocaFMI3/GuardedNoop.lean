import RumocaFMI3.GuardedCalls
import RumocaFMI3.LifecycleGuard

/-! A reusable effect-free suffix after a checked FMI lifecycle guard.
The result follows from execution; it is not a successful-return premise. -/
noncomputable section
namespace Rumoca.FMI3.GuardedCalls
open CTree CMemory CBody
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

theorem unchanged_body (cmd : Command) (env : Locals) (heap : Heap)
    (p : Address) (kind : Kind) (mode : Mode)
    (hi : env "instance" = some (.pointer (some p))) (hn : env "m" = none)
    (ok : env "fmi3OK" = none)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed cmd kind mode) :
    run 4 (.running (Runtime.require cmd ++ [Runtime.ok]) env heap) =
      some (.returned ⟨.integer 0, heap⟩) := by
  rw [show 4 = 3 + 1 from rfl, run_add,
    LifecycleGuard.accept env heap p cmd kind mode [Runtime.ok] hi hn hk hm allowed]
  simp [run, next, Runtime.ok, Runtime.ret, Runtime.v, eval, resolve,
    CBody.bind, constants, ok]

end Rumoca.FMI3.GuardedCalls
end
