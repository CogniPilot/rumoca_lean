import RumocaCore.GALEC.TensorWrites
import ProofAudit.Audit

-- Every explicitly authored declaration in the corresponding source module.
#audit axioms Rumoca.GALEC.TensorWrites.write
#audit axioms Rumoca.GALEC.TensorWrites.read_write
#audit axioms Rumoca.GALEC.TensorWrites.Writes
#audit axioms Rumoca.GALEC.TensorWrites.write_correct
#audit axioms Rumoca.GALEC.TensorWrites.overwrite
#audit axioms Rumoca.GALEC.TensorWrites.overwrite_prefix
#audit axioms Rumoca.GALEC.TensorWrites.overwrite_get
#audit axioms Rumoca.GALEC.TensorWrites.overwrite_frame
#audit axioms Rumoca.GALEC.TensorWrites.overwrite_eq
#audit axioms Rumoca.GALEC.TensorWrites.overwrite_executes
#audit axioms Rumoca.GALEC.TensorWrites.binary
#audit axioms Rumoca.GALEC.TensorWrites.binary_correct
#audit axioms Rumoca.GALEC.TensorWrites.scatter
#audit axioms Rumoca.GALEC.TensorWrites.scatterWith
#audit axioms Rumoca.GALEC.TensorWrites.scatterWith_prefix
#audit axioms Rumoca.GALEC.TensorWrites.scatterWith_get
#audit axioms Rumoca.GALEC.TensorWrites.scatterWith_executes
#audit axioms Rumoca.GALEC.TensorWrites.scatter_prefix
#audit axioms Rumoca.GALEC.TensorWrites.scatter_get
#audit axioms Rumoca.GALEC.TensorWrites.scatter_executes
#audit axioms Rumoca.GALEC.TensorWrites.diagonal
#audit axioms Rumoca.GALEC.TensorWrites.diagonal_get
#audit axioms Rumoca.GALEC.TensorWrites.diagonal_executes
#audit axioms Rumoca.GALEC.TensorWrites.diagonal_prepared
