import RumocaC.Tree

/-! Fixed-storage reservation helper. Its loop examines each atomic Boolean at
most once and returns `count` when no exchange observed a vacant entry. A
concurrent failed scan does not assert that all entries were busy at one instant.
The helper neither allocates objects nor initializes the objects being reserved.
The caller supplies an existing flag array and its valid extent. -/
namespace Rumoca.CAtomicScan
open CTree

def attempt : Stmt := .assign (.id "busy")
  (.call (.id "atomic_exchange")
    [.address (.index (.id "flags") (.id "k")), .cast "_Bool" (.nat 1)])

def selected : Stmt := .branch (.not (.id "busy")) [.ret (some (.id "k"))] []

/-- Both operands have the declared unsigned size type. In particular this
does not introduce a signed integer literal into unsigned arithmetic. -/
def advance : Stmt := .assign (.id "k") (.bin .add (.id "k") (.id "one"))

def scan : Stmt := .whileLoop (.bin .lt (.id "k") (.id "count"))
  [attempt, selected, advance]

def function : Function := {
  signature := ⟨"size_t", "rumoca_reserve_slot",
    [⟨"volatile atomic_bool *", "flags", false⟩, ⟨"size_t", "count", false⟩]⟩
  body := [.declare "size_t" "k" (.nat 0),
    .declare "const size_t" "one" (.nat 1),
    .declare "_Bool" "busy" (.cast "_Bool" (.nat 0)),
    scan, .ret (some (.id "count"))]
  static := true
}

end Rumoca.CAtomicScan
