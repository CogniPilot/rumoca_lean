import RumocaFMI3.AdapterRenderPlan
import RumocaFMI3.TensorFloat64Access
import RumocaFMI3.ConstantFloat64Access

/-! Profile-driven adapter render plan and dispatch data.

The storage `Profile` (`TensorInstance.Profile`) is the single source of truth for
the per-profile adapter data: the presence of the input and output regions, the
prepared kernel entries, the Float64 value-reference dispatch table, the extra
callees the call policy admits, and the eFMI capability. This module pairs a
profile with the model-derived render inputs through `planOf`, and records the
profile's dispatch table (`referencesOf`) and admitted-callee extension
(`calleesOf`).

Each profile's Float64 getter and setter dispatch over exactly the value
references its profile declares: the ordered numeric references of
`TensorFloat64.getArms`/`setArms` and `ConstantFloat64.getArms`/`setArms` are the
`References.get`/`References.set` fields of the tensor and constant profiles,
recovered by `rfl`. The render fields (the model name, the declaration preamble
string, the shared helper prefix and the per-signature body builder) stay
model-derived and are threaded through `planOf`; the C-adapter preamble is a
rendered string whose byte structure is not definitionally derivable from the
profile flags, so it is supplied per model. -/
namespace Rumoca.FMI3
open CTree
open Rumoca.Tensor (Shape)
open Rumoca.FMI3.TensorInstance (Profile References tensorProfile constantProfile)
set_option autoImplicit false

/-- The adapter render plan of a profile: the shared five-piece render built from
the model name (fixing the source-link prefix), the declaration preamble string,
the reused helper prefix and the per-signature body builder. The profile pins the
call-policy and dispatch data (`referencesOf`, `calleesOf`); the render fields are
the model-derived inputs of the shared `RenderPlan`. -/
def planOf (_p : Profile) (name preamble : String)
    (helpers : List CTree.Function) (body : CTree.Signature → CTree.Function) : RenderPlan :=
  { name := name, preamble := preamble, helpers := helpers, body := body }

/-- The render of a profile's plan is the shared `RenderPlan.render`. -/
theorem planOf_render (p : Profile) (name preamble : String)
    (helpers : List CTree.Function) (body : CTree.Signature → CTree.Function)
    (sigs : List CTree.Signature) :
    (planOf p name preamble helpers body).render sigs =
      functionPrefix name ++ "#include \"model.c\"\n" ++ preamble ++
        String.join (helpers.map CTree.Function.render) ++
        String.join (sigs.map fun sig => (body sig).render) := rfl

/-- The Float64 getter/setter value-reference dispatch table declared by a
profile. -/
def referencesOf (p : Profile) : References := p.references

/-- The extra callees a profile's call policy admits beyond the shared scalar
classification: exactly the profile's declared extension. -/
def calleesOf (p : Profile) : List String := p.extraCallees

/-! ### The dispatch tables are the profile references

Each profile's Float64 getter and setter dispatch over exactly the numeric value
references its profile declares, in order. -/

/-- The tensor getter dispatches over the tensor profile's getter references. -/
theorem tensor_getArms_references (shape : Shape) (outputShape : Option Shape) :
    (TensorFloat64.getArms shape outputShape).map Prod.fst = (referencesOf tensorProfile).get := rfl

/-- The tensor setter dispatches over the tensor profile's setter references. -/
theorem tensor_setArms_references (shape : Shape) :
    (TensorFloat64.setArms shape).map Prod.fst = (referencesOf tensorProfile).set := rfl

/-- The constant getter dispatches over the constant profile's getter references. -/
theorem constant_getArms_references (shape : Shape) :
    (ConstantFloat64.getArms shape).map Prod.fst = (referencesOf constantProfile).get := rfl

/-- The constant setter dispatches over the constant profile's setter references. -/
theorem constant_setArms_references (shape : Shape) :
    (ConstantFloat64.setArms shape).map Prod.fst = (referencesOf constantProfile).set := rfl

end Rumoca.FMI3
