import RumocaCore.Modelica.Profile
import ModelicaParser.Certificate
import ProofAudit.Audit

/-! Kernel-checked selection of the admitted example sources and certified
single-fault rejections. Every source below is parsed by the certified general
grammar (`certify_source`); admission is decided by `Profile.select` on the
parsed tree, never by the grammar. -/
namespace Rumoca.Modelica.ProfileChecks

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! ### The admitted example sources select their existing records -/

certify_source integrator "model Integrator
  Real x;
equation
  der(x) = 1;
end Integrator;
"

theorem integrator_selected :
    Profile.select integrator.ast = .ok (.unit ⟨"Integrator", "x", "x", "Integrator"⟩) := by rfl

certify_source tensorSquare "model TensorSquare
  input Real u[2];
  output Real x[2](each start=0, each fixed=true);
  output Real J[2,2];
equation
  der(x) = u .* u;
  J = jacobian (u .* u, u);
end TensorSquare;
"

theorem tensorSquare_selected :
    Profile.select tensorSquare.ast = .ok (.square
      ⟨⟨"TensorSquare", "u", "x", "start", "fixed"⟩,
        .jacobian "J" "x" ⟨"u", "u"⟩ "J" ⟨"jacobian", ⟨"u", "u"⟩, "u"⟩, "TensorSquare"⟩) := by rfl

certify_source constantRates "model ConstantRates
  Real x;
  Real y;
equation
  der(x) = 2.5;
  der(y) = -1;
end ConstantRates;
"

theorem constantRates_selected :
    Profile.select constantRates.ast = .ok (.rates
      ⟨"ConstantRates", "x", "y", [], ⟨"x", "2.5"⟩, [⟨"y", "-1"⟩], "ConstantRates"⟩) := by rfl

/-! ### Certified rejections -/

/- The driven input/output scalar profile is not admitted. -/
certify_source drivenIntegrator "model DrivenIntegrator
  input Real u;
  output Real x(start=0, fixed=true);
equation
  der(x) = u;
end DrivenIntegrator;
"

theorem drivenIntegrator_rejected :
    Profile.select drivenIntegrator.ast =
      .error ⟨2, "the unit profile declares exactly one state"⟩ := by rfl

/- The driven array body is not admitted: the square profile requires its
Jacobian output. -/
certify_source arrayDriven "model ArrayDriven
  input Real u[2];
  output Real x[2](each start=0, each fixed=true);
equation
  der(x) = u;
end ArrayDriven;
"

theorem arrayDriven_rejected :
    Profile.select arrayDriven.ast =
      .error ⟨2, "the unit profile declares exactly one state"⟩ := by rfl

/- An undeclared right-hand-side reference. -/
certify_source undeclared "model M Real x; equation der(x) = u; end M;"
theorem undeclared_rejected :
    Profile.select undeclared.ast = .error ⟨11, "the unit derivative must be a number"⟩ := by rfl

/- An algebraic equation. -/
certify_source algebraic "model M Real x; equation x = 1; end M;"
theorem algebraic_rejected :
    Profile.select algebraic.ast =
      .error ⟨6, "the left side must be der applied to one declared name"⟩ := by rfl

/- The reversed equation `1 = der(x)`. -/
certify_source reversed "model M Real x; equation 1 = der(x); end M;"
theorem reversed_rejected :
    Profile.select reversed.ast =
      .error ⟨6, "the left side must be der applied to one declared name"⟩ := by rfl

/- A scalar pointwise product. -/
certify_source scalarProduct "model M Real x; equation der(x) = x .* x; end M;"
theorem scalarProduct_rejected :
    Profile.select scalarProduct.ast = .error ⟨11, "the unit derivative must be a number"⟩ := by rfl

/- `der` in a right-hand side. -/
certify_source nestedDer "model M Real x; equation der(x) = der(x); end M;"
theorem nestedDer_rejected :
    Profile.select nestedDer.ast = .error ⟨11, "the unit derivative must be a number"⟩ := by rfl

/- A Boolean right-hand side. -/
certify_source booleanRate "model M Real x; equation der(x) = true; end M;"
theorem booleanRate_rejected :
    Profile.select booleanRate.ast = .error ⟨11, "the unit derivative must be a number"⟩ := by rfl

/- Subscripts on a number. -/
certify_source indexedNumber "model M Real x; equation der(x) = 1[2]; end M;"
theorem indexedNumber_rejected :
    Profile.select indexedNumber.ast = .error ⟨11, "the unit derivative must be a number"⟩ := by rfl

/- A parenthesized right-hand side. -/
certify_source parenthesized "model M Real x; equation der(x) = (1); end M;"
theorem parenthesized_rejected :
    Profile.select parenthesized.ast = .error ⟨11, "the unit derivative must be a number"⟩ := by rfl

/- A number spelled other than `1`. -/
certify_source decimalUnit "model M Real x; equation der(x) = 1.0; end M;"
theorem decimalUnit_rejected :
    Profile.select decimalUnit.ast = .error ⟨11, "the unit derivative may not be 1.0"⟩ := by rfl

/- A dotted type name. -/
certify_source dottedType "model M Modelica.Real x; equation der(x) = 1; end M;"
theorem dottedType_rejected :
    Profile.select dottedType.ast = .error ⟨2, "the state declaration must have type Real"⟩ := by rfl

/- A dotted reference. -/
certify_source dottedReference "model M Real x; equation der(a.x) = 1; end M;"
theorem dottedReference_rejected :
    Profile.select dottedReference.ast =
      .error ⟨8, "the differentiated name must be a plain name"⟩ := by rfl

/- A global reference. -/
certify_source globalReference "model M Real x; equation der(.x) = 1; end M;"
theorem globalReference_rejected :
    Profile.select globalReference.ast =
      .error ⟨8, "the differentiated name must be a plain name"⟩ := by rfl

/- Two class definitions. -/
certify_source twoClasses
  "model M Real x; equation der(x) = 1; end M; model N Real x; equation der(x) = 1; end N;"
theorem twoClasses_rejected :
    Profile.select twoClasses.ast = .error ⟨16, "only one class definition is admitted"⟩ := by rfl

/- Two names in one component clause. -/
certify_source twoNames "model M Real x, y; equation der(x) = 1; end M;"
theorem twoNames_rejected :
    Profile.select twoNames.ast =
      .error ⟨3, "the state declaration must declare exactly one name"⟩ := by rfl

/- A predefined type name as a declared name. -/
certify_source predefinedName "model M Real Real; equation der(Real) = 1; end M;"
theorem predefinedName_rejected :
    Profile.select predefinedName.ast =
      .error ⟨3, "the state declaration may not be the predefined type name Real"⟩ := by rfl

/- An input prefix on a state. -/
certify_source inputState "model M input Real x; equation der(x) = 1; end M;"
theorem inputState_rejected :
    Profile.select inputState.ast =
      .error ⟨2, "the state declaration has the wrong input/output prefix"⟩ := by rfl

/- A start modification on a unit state. -/
certify_source startModified "model M Real x(start = 1); equation der(x) = 1; end M;"
theorem startModified_rejected :
    Profile.select startModified.ast =
      .error ⟨4, "the state declaration may not have a modification"⟩ := by rfl

/- An array state in the unit profile. -/
certify_source arrayState "model M Real x[2]; equation der(x) = 1; end M;"
theorem arrayState_rejected :
    Profile.select arrayState.ast = .error ⟨4, "the state declaration must be scalar"⟩ := by rfl

/- Two equation sections. -/
certify_source twoSections "model M Real x; equation der(x) = 1; equation end M;"
theorem twoSections_rejected :
    Profile.select twoSections.ast = .error ⟨13, "only one equation section is admitted"⟩ := by rfl

/- An unsigned integer rate, which was never a rate literal. -/
certify_source integerRate
  "model M Real x; Real y; equation der(x) = 2; der(y) = -1; end M;"
theorem integerRate_rejected :
    Profile.select integerRate.ast = .error ⟨14, "the rate may not be 2"⟩ := by rfl

/- A rate with a trailing point, an MLS number spelling not admitted as a rate. -/
certify_source trailingPoint
  "model M Real x; Real y; equation der(x) = 2.; der(y) = -1; end M;"
theorem trailingPoint_rejected :
    Profile.select trailingPoint.ast = .error ⟨14, "the rate may not be 2."⟩ := by rfl

/- A rate with a leading point, an MLS number spelling not admitted as a rate. -/
certify_source leadingPoint
  "model M Real x; Real y; equation der(x) = 2.5; der(y) = -.5; end M;"
theorem leadingPoint_rejected :
    Profile.select leadingPoint.ast = .error ⟨21, "the rate may not be -.5"⟩ := by rfl

/- A rate sign is the leading sign of the arithmetic expression; lexical units
may be separated by white space. -/
certify_source separatedSign
  "model M Real x; Real y; equation der(x) = 2.5; der(y) = - 1; end M;"
theorem separatedSign_selected :
    Profile.select separatedSign.ast =
      .ok (.rates ⟨"M", "x", "y", [], ⟨"x", "2.5"⟩, [⟨"y", "-1"⟩], "M"⟩) := by rfl

/- A comment is lexed with its range but is not admitted yet: no selection
admits a commented source. -/
certify_source commented "model M // integrator
  Real x;
equation
  der(x) = 1;
end M;
"
theorem commented_rejected (parsed : AST.selection.Parsed commented.source) : False := by
  have same : parsed.tree = commented.parsed := Modelica.Parsed.unique _ _
  have uncommented := parsed.uncommented
  rw [same] at uncommented
  exact absurd uncommented (by decide)

/- A number token satisfies every `IDENT` position of the grammar; static
semantics rejects it as a name. -/
certify_source numberName "model 1 Real x; equation der(x) = 1; end 1;"
theorem numberName_rejected :
    Profile.select numberName.ast =
      .error ⟨1, "the model name must be an identifier, not the number 1"⟩ := by rfl

/- An empty stored definition. -/
certify_source empty ""
theorem empty_rejected :
    Profile.select empty.ast = .error ⟨0, "expected one class definition"⟩ := by rfl

#audit axioms integrator_selected
#audit axioms tensorSquare_selected
#audit axioms constantRates_selected
#audit axioms drivenIntegrator_rejected
#audit axioms arrayDriven_rejected
#audit axioms undeclared_rejected
#audit axioms algebraic_rejected
#audit axioms reversed_rejected
#audit axioms scalarProduct_rejected
#audit axioms nestedDer_rejected
#audit axioms booleanRate_rejected
#audit axioms indexedNumber_rejected
#audit axioms parenthesized_rejected
#audit axioms decimalUnit_rejected
#audit axioms dottedType_rejected
#audit axioms dottedReference_rejected
#audit axioms globalReference_rejected
#audit axioms twoClasses_rejected
#audit axioms twoNames_rejected
#audit axioms predefinedName_rejected
#audit axioms inputState_rejected
#audit axioms startModified_rejected
#audit axioms arrayState_rejected
#audit axioms twoSections_rejected
#audit axioms integerRate_rejected
#audit axioms trailingPoint_rejected
#audit axioms leadingPoint_rejected
#audit axioms numberName_rejected
#audit axioms separatedSign_selected
#audit axioms commented_rejected
#audit axioms empty_rejected

end Rumoca.Modelica.ProfileChecks
