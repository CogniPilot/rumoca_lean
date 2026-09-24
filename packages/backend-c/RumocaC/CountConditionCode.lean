import RumocaC.Tree

/-! Shared size-count predicates using the existing C expression syntax.
This spelling alone is not a native promotion or essential-type certificate. -/
namespace Rumoca.CCountConditions
open CTree

def sizeZero : Expr := .cast "size_t" (.nat 0)
def nonzero (count : Expr) : Expr := .bin .ne count sizeZero

end Rumoca.CCountConditions
