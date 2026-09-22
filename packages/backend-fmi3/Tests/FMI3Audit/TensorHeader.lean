import RumocaFMI3.TensorHeader
import ProofAudit.Audit

-- Actual interface facts: require coherent CInterface-dependent rebuild.
#audit axioms Rumoca.FMI3.TensorHeader.double_pointer
#audit axioms Rumoca.FMI3.TensorHeader.const_double_pointer
#audit axioms Rumoca.FMI3.TensorHeader.static_binary
#audit axioms Rumoca.FMI3.TensorHeader.static_fill
#audit axioms Rumoca.FMI3.TensorHeader.fenv_binary
#audit axioms Rumoca.FMI3.TensorHeader.fenv_fill
#audit axioms Rumoca.FMI3.TensorHeader.runtime_binary
#audit axioms Rumoca.FMI3.TensorHeader.runtime_fill
#audit axioms Rumoca.FMI3.TensorHeader.fenv_step_types
#audit axioms Rumoca.FMI3.TensorHeader.runtime_step_types
#audit axioms Rumoca.FMI3.TensorHeader.fenv_nearest
#audit axioms Rumoca.FMI3.TensorHeader.runtime_nearest
#audit axioms Rumoca.FMI3.TensorHeader.fenv_tensor
#audit axioms Rumoca.FMI3.TensorHeader.runtime_tensor
#audit axioms Rumoca.FMI3.TensorHeader.static_library
#audit axioms Rumoca.FMI3.TensorHeader.fenv_library
#audit axioms Rumoca.FMI3.TensorHeader.runtime_library
