/-! Provenance vocabulary for the direct rendering of prepared Solve
instructions. Interface status and function-entry policy belong to adapters. -/
namespace Rumoca.CAlgorithm

inductive Rule where
  | registerDeclaration
  | literalConversion
  | assignment
  | storageAccess
  deriving Repr, DecidableEq

end Rumoca.CAlgorithm
