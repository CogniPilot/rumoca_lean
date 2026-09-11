import RumocaCore.IR.Solve

/-! The scalar source, residual and executable IR stages are defined in
`IR.Flat`, `IR.DAE` and `IR.Solve`. Actual model occurrences require checked
source contexts and origin traces; pure expressions retain independent meaning.
No solver or target format is selected by the provenance machinery. -/
