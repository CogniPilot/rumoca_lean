import ProofAudit.Audit

-- The checker itself is a trusted boundary: keep one acceptance/rejection check.
/-- info: True.intro depends on axioms: [] -/
#guard_msgs in
#audit axioms True.intro

/-- error: unapproved axiom in Lean.ofReduceBool: Lean.ofReduceBool -/
#guard_msgs in
#audit axioms Lean.ofReduceBool
