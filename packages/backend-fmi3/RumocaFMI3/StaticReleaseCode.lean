import RumocaC.Tree

/-! Constant-work release of permanent instance storage. Creation must store
the bounded slot index before returning a handle. A null handle has no effect.
No object lifetime is ended: only its reservation flag is released. -/
namespace Rumoca.FMI3.StaticRelease
open CTree

def clear : Stmt := .eval (.call (.id "atomic_store") [
  .address (.index (.id "rumoca_instance_flags") (.field (.id "m") "slot" true)),
  .cast "_Bool" (.nat 0)])

def guard : Stmt := .branch (.bin .ne (.id "m") .nullPointer) [clear] []

def function : Function := {
  signature := ⟨"void", "fmi3FreeInstance", [⟨"fmi3Instance", "instance", false⟩]⟩
  body := [.declare "Instance *" "m" (.cast "Instance *" (.id "instance")), guard, .ret none]
}

end Rumoca.FMI3.StaticRelease
