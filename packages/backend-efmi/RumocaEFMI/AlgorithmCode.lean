import RumocaCore.GALEC.IR

/-! Thin Algorithm Code rendering from the checked DAE-derived GALEC product.
Canonical names are deliberately fixed in the tiny profile. There is no name
resolution, equation solving, or selection of a numerical policy in this file. -/
namespace Rumoca.EFMI

def expression (stateName : String) : GALEC.Expr Rumoca.Tensor.scalar → String
  | .state => "self." ++ stateName
  | .zero => "0.0"
  | .one => "1.0"
  | .add a b => "(" ++ expression stateName a ++ " + " ++ expression stateName b ++ ")"

def assignment (body : Option (GALEC.Expr Rumoca.Tensor.scalar)) : String :=
  body.elim "" (fun expr => "        self.x := " ++ expression "x" expr ++ ";\n")

def renderBlock (b : GALEC.Block Rumoca.Tensor.scalar) : String :=
  "block UnitIntegrator\n    output Real x;\nprotected\n    constant Real samplePeriod;\npublic\n" ++
  "    method Startup\n    algorithm\n" ++ assignment b.startup ++
  "        self.samplePeriod := " ++ expression "samplePeriod" b.startupPeriod ++
  ";\n    end Startup;\n" ++
  "    method Recalibrate\n    algorithm\n" ++ assignment b.recalibrate ++
  "    end Recalibrate;\n    method DoStep\n    algorithm\n" ++ assignment b.doStep ++
  "    end DoStep;\nend UnitIntegrator;\n"

def renderAlgorithm (m : GALEC.Model source) : String := renderBlock m.block

def unitSource : String := renderBlock GALEC.unitBlock

theorem emission_is_unit (m : GALEC.Model source) : renderAlgorithm m = unitSource := by
  rw [renderAlgorithm, m.profile]
  rfl

end Rumoca.EFMI
