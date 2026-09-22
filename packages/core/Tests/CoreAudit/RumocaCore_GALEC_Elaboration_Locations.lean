import RumocaCore.GALEC.Elaboration.Locations
import ProofAudit.Audit

-- Public authored roots and the retained source-address audit roots.
#audit axioms Rumoca.GALEC.Elaboration.Location
#audit axioms Rumoca.GALEC.Elaboration.Read.location
#audit axioms Rumoca.GALEC.Elaboration.Location.get
#audit axioms Rumoca.GALEC.Elaboration.Location.Evaluates
#audit axioms Rumoca.GALEC.Elaboration.Location.lowering_sound
#audit axioms Rumoca.GALEC.Elaboration.Location.evaluates_unique
#audit axioms Rumoca.GALEC.Elaboration.Location.lowering_correct
#audit axioms Rumoca.GALEC.Elaboration.ReadLowering.evaluates_iff_location
#audit axioms Rumoca.GALEC.Elaboration.Location.mk
#audit axioms Rumoca.GALEC.Elaboration.Location.shape
#audit axioms Rumoca.GALEC.Elaboration.Location.access
#audit axioms Rumoca.GALEC.Elaboration.Location.coordinate
#audit axioms Rumoca.GALEC.Elaboration.Location.Evaluates.indexed
