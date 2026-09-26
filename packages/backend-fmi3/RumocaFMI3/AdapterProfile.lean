import RumocaFMI3.AdapterRenderPlan
import RumocaFMI3.TensorInstanceStorage

/-! Profile-driven adapter render plan and dispatch data.

The storage `Profile` (`TensorInstance.Profile`) is the single source of truth for
the per-profile adapter data: the presence of the input and output regions, the
prepared kernel entries, the extra callees the call policy admits, and the eFMI
capability. This module pairs a profile with the model-derived render inputs
through `planOf`, and records the profile's admitted-callee extension
(`calleesOf`). The Float64 value-reference dispatch tables are not profile data:
they are built from each model's declared interface (`Float64Table.getArms`,
`Float64Table.setArms`). The render fields (the model name, the declaration
preamble string, the shared helper prefix and the per-signature body builder)
stay model-derived and are threaded through `planOf`; the C-adapter preamble is
a rendered string whose byte structure is not definitionally derivable from the
profile flags, so it is supplied per model. -/
namespace Rumoca.FMI3
open CTree
open Rumoca.FMI3.TensorInstance (Profile)
set_option autoImplicit false

/-- The adapter render plan of a profile: the shared five-piece render built from
the model name (fixing the source-link prefix), the declaration preamble string,
the reused helper prefix and the per-signature body builder. The profile pins the
call-policy data (`calleesOf`); the render fields are the model-derived inputs of
the shared `RenderPlan`. -/
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

/-- The extra callees a profile's call policy admits beyond the shared scalar
classification: exactly the profile's declared extension. -/
def calleesOf (p : Profile) : List String := p.extraCallees

end Rumoca.FMI3
