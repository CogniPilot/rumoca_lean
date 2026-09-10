import RumocaEFMI.CPrinterProofs
import RumocaEFMI.ProductionProofs

namespace Rumoca.EFMI.CSyntax

def unitProgram : Program :=
  ⟨⟨"UnitIntegrator_Startup", "self",
    [.declare "v0" (.atom .zero), .assign (.member "self" "x") (.atom (.variable "v0")),
     .declare "v1" (.atom .one), .assign (.member "self" "samplePeriod") (.atom (.variable "v1"))]⟩,
   ⟨"UnitIntegrator_Recalibrate", "self",
    [.assign (.member "self" "x") (.atom (.member "self" "x"))]⟩,
   ⟨"UnitIntegrator_DoStep", "self",
    [.declare "v0" (.atom .one),
     .declare "v1" (.add (.member "self" "x") (.variable "v0")),
     .assign (.member "self" "x") (.atom (.variable "v1"))]⟩⟩

theorem unit_tree : unitProgram.tree = Production.unitModule := rfl

def unitText : String := Production.preamble ++
  "EfmiStatus UnitIntegrator_Startup(Model * self) {\n  double v0 = ((double)0);\n  (self->x) = v0;\n  double v1 = ((double)1);\n  (self->samplePeriod) = v1;\n  return 0;\n}\n\n" ++
  "EfmiStatus UnitIntegrator_Recalibrate(Model * self) {\n  (self->x) = (self->x);\n  return 0;\n}\n\n" ++
  "EfmiStatus UnitIntegrator_DoStep(Model * self) {\n  double v0 = ((double)1);\n  double v1 = ((self->x) + v0);\n  (self->x) = v1;\n  return 0;\n}\n\n"

set_option maxRecDepth 10000 in
theorem render_unit : Production.unitModule.render = unitText := by
  simp only [Production.Module.render, Production.unitModule, Production.function,
    Production.stateField, CTree.Function.render, CTree.Signature.render,
    CTree.Parameter.render, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    CTree.Stmt.render, CTree.Expr.render, CTree.BinOp.render]
  decide +kernel

theorem print_denotes (model : Solve.Algorithm.Model source) (module : Production.Module)
    (lowered : Production.lower model = .ok module) :
    ∃ printed, printed.tree = module ∧ Denotes module.render printed := by
  have hm := (Production.lower_is_unit model).symm.trans lowered
  cases Except.ok.inj hm
  exact ⟨unitProgram, unit_tree, unit_tree ▸ program_render unitProgram (by decide +kernel)⟩

end Rumoca.EFMI.CSyntax
