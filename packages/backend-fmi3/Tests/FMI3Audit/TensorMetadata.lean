import RumocaFMI3.TensorMetadata
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.TensorMetadata.

#audit axioms Rumoca.FMI3.TensorMetadata.text_toString
#audit axioms Rumoca.FMI3.TensorMetadata.startEntries_length
#audit axioms Rumoca.FMI3.TensorMetadata.startValue_text
#audit axioms Rumoca.FMI3.TensorMetadata.valid
#audit axioms Rumoca.FMI3.TensorMetadata.document
#audit axioms Rumoca.FMI3.TensorMetadata.valueReferences_eq
#audit axioms Rumoca.FMI3.TensorMetadata.valueReferences_nodup
#audit axioms Rumoca.FMI3.TensorMetadata.dimStarts_dimensions
#audit axioms Rumoca.FMI3.TensorMetadata.stateVar_dim_product
#audit axioms Rumoca.FMI3.TensorMetadata.inputVar_dim_product
#audit axioms Rumoca.FMI3.TensorMetadata.derivativeVar_dim_product
#audit axioms Rumoca.FMI3.TensorMetadata.outputVar_dim_product
#audit axioms Rumoca.FMI3.TensorMetadata.derivative_references_state
#audit axioms Rumoca.FMI3.TensorMetadata.structure_references_declared
#audit axioms Rumoca.FMI3.TensorMetadata.structure_dependencies_declared
#audit axioms Rumoca.FMI3.TensorMetadata.modelIdentifiers_decode
#audit axioms Rumoca.FMI3.TensorMetadata.token_attribute
#audit axioms Rumoca.FMI3.TensorMetadata.constantToken_attribute
#audit axioms Rumoca.FMI3.TensorMetadata.constantStateVar_valid
#audit axioms Rumoca.FMI3.TensorMetadata.constantDerivativeVar_valid
#audit axioms Rumoca.FMI3.TensorMetadata.constantVariableNodes_valid
#audit axioms Rumoca.FMI3.TensorMetadata.constantStructureNodes_valid
#audit axioms Rumoca.FMI3.TensorMetadata.constant_valid
#audit axioms Rumoca.FMI3.TensorMetadata.constant_document
#audit axioms Rumoca.FMI3.TensorMetadata.constantValueReferences_eq
#audit axioms Rumoca.FMI3.TensorMetadata.constantValueReferences_nodup
#audit axioms Rumoca.FMI3.TensorMetadata.constantStateVar_dim_product
#audit axioms Rumoca.FMI3.TensorMetadata.constantDerivativeVar_dim_product
#audit axioms Rumoca.FMI3.TensorMetadata.constant_derivative_references_state
#audit axioms Rumoca.FMI3.TensorMetadata.constant_structure_references_declared
#audit axioms Rumoca.FMI3.TensorMetadata.constant_structure_dependencies_empty
#audit axioms Rumoca.FMI3.TensorMetadata.constant_modelIdentifiers_decode
