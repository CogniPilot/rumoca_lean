import RumocaC.Algorithm
import RumocaC.Tree
import RumocaC.Codegen
import RumocaEFMI.CHeader

/-! Direct instruction rendering from the prepared Solve algorithm. Every
register instruction becomes one C declaration; return assigns the selected
instance field. This backend neither eliminates registers nor redoes solving.
The current C storage profile supports rank-zero tensors only. -/
namespace Rumoca.EFMI.Production
open Rumoca.Tensor Rumoca.Solve.Tensor Rumoca.CTree Rumoca.CAlgorithm

def initialName (field : String) : Names [scalar]
  | _, .here => .field (.id "self") field true

def stateField (name : String) : Expr := .field (.id "self") name true

/-- The error-free unit profile exposes its per-call status through the
instance field declared in the eFMI manifest and the matching C return value. -/
def function (name : String) (body : List Stmt) : Function :=
  ⟨⟨"EfmiStatus", name, [⟨"Model *", "self", false⟩]⟩,
    .assign (stateField CHeader.statusName) (.nat 0) ::
      (body ++ [.ret (some (stateField CHeader.statusName))]), false⟩

structure Module where
  startup : Function
  recalibrate : Function
  doStep : Function

def Module.method (module : Module) : GALEC.Method → Function
  | .startup => module.startup
  | .recalibrate => module.recalibrate
  | .doStep => module.doStep

def lowerBlock (block : Solve.Algorithm.Block scalar) : Except String Module := do
  let (nextId, startup) ← emitProgram block.startup (initialName "x") (stateField "x") 0
  let (_, period) ← emitProgram block.startupPeriod (initialName "samplePeriod")
    (stateField "samplePeriod") nextId
  let (_, recalibrate) ← emitProgram block.recalibrate (initialName "x") (stateField "x") 0
  let (_, doStep) ← emitProgram block.doStep (initialName "x") (stateField "x") 0
  return ⟨function "UnitIntegrator_Startup" (startup ++ period),
    function "UnitIntegrator_Recalibrate" recalibrate,
    function "UnitIntegrator_DoStep" doStep⟩

def lower (model : Solve.Algorithm.Model source) : Except String Module := lowerBlock model.block

/-- The fixed preamble declares the storage and finite binary64 target profile.
Its correspondence to C preprocessing and object layout is explicitly reviewed,
not a theorem about the host C compiler or byte-addressed machine ABI. -/
def preamble : String := C.preamble ++ CHeader.render

def Module.render (module : Module) : String := preamble ++
  module.startup.render ++ module.recalibrate.render ++ module.doStep.render

end Rumoca.EFMI.Production
