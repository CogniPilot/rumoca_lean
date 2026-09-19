import Rumoca.FMI3CSProtocol
import ProofAudit.Audit

-- Axiom audit for the roots defined in Rumoca.FMI3CSProtocol.

#audit axioms Rumoca.FMI3.CSProtocol.Ready.initialization
#audit axioms Rumoca.FMI3.CSProtocol.Ready.simulation
#audit axioms Rumoca.FMI3.CSProtocol.CycleContract.completed
#audit axioms Rumoca.FMI3.CSProtocol.cycle_contract
#audit axioms Rumoca.FMI3.CSProtocol.CycleContract.progress
#audit axioms Rumoca.FMI3.CSProtocol.CycleContract.restarted
#audit axioms Rumoca.FMI3.CSProtocol.correct
#audit axioms Rumoca.FMI3.CSProtocol.interrupted_correct
#audit axioms Rumoca.FMI3.CSProtocol.Contract.stopped_source
#audit axioms Rumoca.FMI3.CSProtocol.Contract.progress_source
#audit axioms Rumoca.FMI3.CSProtocol.Contract.released
