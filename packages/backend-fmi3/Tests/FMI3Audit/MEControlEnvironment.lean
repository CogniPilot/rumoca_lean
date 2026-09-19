import RumocaFMI3.MEControlEnvironment
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.MEControlEnvironment.

#audit axioms Rumoca.FMI3.MEControlEnvironment.null_call
#audit axioms Rumoca.FMI3.MEControlEnvironment.EntryControl.body_agrees
#audit axioms Rumoca.FMI3.MEControlEnvironment.EntryControl.call_behaviors
#audit axioms Rumoca.FMI3.MEControlEnvironment.EntryControl.null_behaviors
#audit axioms Rumoca.FMI3.MEControlEnvironment.EntryControl.quiet_correct
#audit axioms Rumoca.FMI3.MEControlEnvironment.EntryControl.suppressed_correct
#audit axioms Rumoca.FMI3.MEControlEnvironment.EntryControl.logged_correct
#audit axioms Rumoca.FMI3.MEControlEnvironment.CompletedControl.body_agrees
#audit axioms Rumoca.FMI3.MEControlEnvironment.CompletedControl.call_behaviors
#audit axioms Rumoca.FMI3.MEControlEnvironment.CompletedControl.null_behaviors
#audit axioms Rumoca.FMI3.MEControlEnvironment.CompletedControl.quiet_correct
#audit axioms Rumoca.FMI3.MEControlEnvironment.CompletedControl.suppressed_correct
#audit axioms Rumoca.FMI3.MEControlEnvironment.CompletedControl.logged_correct
#audit axioms Rumoca.FMI3.MEControlEnvironment.DiscreteControl.body_agrees
#audit axioms Rumoca.FMI3.MEControlEnvironment.DiscreteControl.call_behaviors
#audit axioms Rumoca.FMI3.MEControlEnvironment.DiscreteControl.null_behaviors
#audit axioms Rumoca.FMI3.MEControlEnvironment.DiscreteControl.quiet_correct
#audit axioms Rumoca.FMI3.MEControlEnvironment.DiscreteControl.suppressed_correct
#audit axioms Rumoca.FMI3.MEControlEnvironment.DiscreteControl.logged_correct
#audit axioms Rumoca.FMI3.MEControlEnvironment.TimeControl.suppressed_correct
#audit axioms Rumoca.FMI3.MEControlEnvironment.TimeControl.logged_correct
