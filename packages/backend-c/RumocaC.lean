import RumocaC.Algorithm
import RumocaC.Tree
import RumocaC.Codegen

/-! C generation API: `Rumoca.C.lower` consumes Solve IR; `Rumoca.C.render`
serializes its typed target. `CAlgorithm.emitProgram` emits prepared tensor
Solve algorithm instructions for a wrapper-supplied register/store layout. Import RumocaC.Statements for backend proofs. -/
