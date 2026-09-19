import Rumoca.FMI3MEProtocol
import ProofAudit.Audit

-- Axiom audit for the roots defined in Rumoca.FMI3MEProtocol.

#audit axioms Rumoca.FMI3.MEProtocol.Ready.initialization
#audit axioms Rumoca.FMI3.MEProtocol.Ready.simulation
#audit axioms Rumoca.FMI3.MEProtocol.CycleContract.completed
#audit axioms Rumoca.FMI3.MEProtocol.cycle_contract
#audit axioms Rumoca.FMI3.MEProtocol.CycleContract.progress
#audit axioms Rumoca.FMI3.MEProtocol.CycleContract.restarted
#audit axioms Rumoca.FMI3.MEProtocol.interrupted_correct
#audit axioms Rumoca.FMI3.MEProtocol.correct
#audit axioms Rumoca.FMI3.MEProtocol.Contract.stopped_source
#audit axioms Rumoca.FMI3.MEProtocol.Contract.progress_source
#audit axioms Rumoca.FMI3.MEProtocol.Contract.released
