import RumocaEFMI.StartupOrigins
import RumocaC.MappedFunction

/-! The production exporter uses this map while rendering its actual lowered
module. Only Startup is annotated in this increment; the header and remaining
methods keep their existing text and receive no invented source locations. -/
namespace Rumoca.EFMI.Production.StartupMap
open Rumoca.CTree Printed
open Printed.Document (text)
local infixl:65 " <+> " => Document.append

structure Emission (model : Solve.Algorithm.Model source) where
  module : Module
  lowered : lower model = .ok module

theorem Emission.module_eq (emission : Emission model) : emission.module = unitModule :=
  (Except.ok.inj ((lower_is_unit model).symm.trans emission.lowered)).symm

/-- All annotation inputs come from the stored Solve trace. The proof changes
the C syntax index and is erased by native compilation. -/
def Emission.startup (emission : Emission model) :
    Function.Origins (StartupOrigins.inputs model).outputTable emission.module.startup :=
  emission.module_eq.symm ▸ (StartupOrigins.inputs model).trace

def Emission.document (emission : Emission model) :
    Document (Origin (StartupOrigins.inputs model).outputTable) :=
  text preamble <+> emission.startup.document <+>
    text (emission.module.recalibrate.render ++ emission.module.doStep.render)

theorem Emission.document_render (emission : Emission model) :
    emission.document.render = emission.module.render := by
  simp only [document, Document.render_append, Document.render_text,
    Function.Origins.document_render, Module.render, String.append_assoc]

def emit (model : Solve.Algorithm.Model source) : Except String (Emission model) :=
  match lowered : lower model with
  | .error message => .error message
  | .ok module => .ok ⟨module, lowered⟩

theorem emit_is_unit (model : Solve.Algorithm.Model source) :
    emit model = .ok ⟨unitModule, lower_is_unit model⟩ := by
  unfold emit
  split
  · rename_i message failed
    have impossible := (lower_is_unit model).symm.trans failed
    cases impossible
  · rename_i module lowered
    have same := Except.ok.inj ((lower_is_unit model).symm.trans lowered)
    cases same
    rfl

theorem emit_success (model : Solve.Algorithm.Model source) :
    ∃ emission, emit model = .ok emission := ⟨_, emit_is_unit model⟩

theorem render_unchanged (model : Solve.Algorithm.Model source) :
    (fun emission => emission.document.render) <$> emit model = Module.render <$> lower model := by
  unfold emit
  split <;> simp_all only [Functor.map, Except.map, Emission.document_render]

end Rumoca.EFMI.Production.StartupMap
