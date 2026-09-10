import RumocaC.Tree

/-! Shared C construction for counted tensor loops. Only existing prepared
operations and their count are rendered here; no tensor elements are listed. -/
namespace Rumoca.CLoops
open CTree

def counterStep (counter : String) : Stmt :=
  .assign (.id counter) (.bin .add (.id counter) (.nat 1))

def loop (counter : String) (count : Expr) (body : List Stmt) : Stmt :=
  .whileLoop (.bin .lt (.id counter) count) (body ++ [counterStep counter])

def counted (counter : String) (count : Expr) (body : List Stmt) : List Stmt :=
  [.declare "size_t" counter (.nat 0), loop counter count body]

end Rumoca.CLoops
