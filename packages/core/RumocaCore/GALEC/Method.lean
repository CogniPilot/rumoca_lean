/-! The three lifecycle methods of an eFMI Algorithm Code block. -/
namespace Rumoca.GALEC

inductive Method where
  | startup | recalibrate | doStep
  deriving Repr, BEq, DecidableEq

end Rumoca.GALEC
