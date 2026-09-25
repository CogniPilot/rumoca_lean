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

/-- The explicit unit-profile C tree used by the independent execution contract. -/
def unitModule : Module :=
  ⟨function (GALEC.Names.function GALEC.Names.unitBlock .startup)
    [.declare "double" "v0" (.cast "double" (.nat 0)),
     .assign (stateField GALEC.Names.state) (.id "v0"),
     .declare "double" "v1" (.cast "double" (.nat 1)),
     .assign (stateField GALEC.Names.clock) (.id "v1")],
   function (GALEC.Names.function GALEC.Names.unitBlock .recalibrate) [.assign (stateField GALEC.Names.state) (stateField GALEC.Names.state)],
   function (GALEC.Names.function GALEC.Names.unitBlock .doStep)
    [.declare "double" "v0" (.cast "double" (.nat 1)),
     .declare "double" "v1" (.bin .add (stateField GALEC.Names.state) (.id "v0")),
     .assign (stateField GALEC.Names.state) (.id "v1")]⟩


def lowerBlock (block : Solve.Algorithm.Block scalar) : Except String Module := do
  let (nextId, startup) ← emitProgram block.startup (initialName GALEC.Names.state) (stateField GALEC.Names.state) 0
  let (_, period) ← emitProgram block.startupPeriod (initialName GALEC.Names.clock)
    (stateField GALEC.Names.clock) nextId
  let (_, recalibrate) ← emitProgram block.recalibrate (initialName GALEC.Names.state) (stateField GALEC.Names.state) 0
  let (_, doStep) ← emitProgram block.doStep (initialName GALEC.Names.state) (stateField GALEC.Names.state) 0
  return ⟨function (GALEC.Names.function GALEC.Names.unitBlock .startup) (startup ++ period),
    function (GALEC.Names.function GALEC.Names.unitBlock .recalibrate) recalibrate,
    function (GALEC.Names.function GALEC.Names.unitBlock .doStep) doStep⟩

def lower (model : Solve.Algorithm.Model source) : Except String Module := lowerBlock model.block

theorem lower_is_unit (model : Solve.Algorithm.Model source) :
    lower model = .ok unitModule := by
  unfold lower
  rw [model.profile]
  rfl


/-- The fixed preamble declares the storage and finite binary64 target profile.
Its correspondence to C preprocessing and object layout is explicitly reviewed,
not a theorem about the host C compiler or byte-addressed machine ABI. -/
def preamble : String := C.preamble ++ CHeader.render

def Module.render (module : Module) : String := preamble ++
  module.startup.render ++ module.recalibrate.render ++ module.doStep.render

end Rumoca.EFMI.Production
