import RumocaFMI3.TensorFunctions
import RumocaFMI3.ConstantFloat64Access
import RumocaFMI3.ConstantDerivative
import RumocaFMI3.ConstantDoStep
import RumocaFMI3.ConstantInstanceRhs
import RumocaFMI3.AdapterProfile
import RumocaCore.Solve.ConstantFMI3

/-! The constant-rate (`G01`) FMI 3 adapter function list, the constant analog of
`TensorFunctions.functions`. Each pinned header signature renders either a
constant-specific behavioral body (the Float64 accessors, the constant derivative
getter and the constant `fmi3DoStep`) or the profile-independent tensor body
instantiated at the constant state shape (lifecycle modes, free, the reserved-record
factory over the constant token, count queries, time, reset, nominals and the
continuous-state copies), or, for every model-independent behavioral and
unsupported/absent-type function, the same scalar body the tensor renderer emits
(`Runtime.function model sig`).

The helper prefix (`TensorFunctions.helpers`) is reused verbatim: the constant
bodies call the shared `fail` diagnostic and the two static-factory helpers, and no
scalar `model_rhs`/`model_advance` wrapper. The declaration preamble is the
constant storage preamble: the shared header inclusion block, the constant-rate
instance record layout (`TensorStorage.storageRenderG shape false false`, no input
and no output region) and the forward declarations of the three constant kernel
entries `rumoca_constant_rhs`/`rumoca_constant_step`/`rumoca_constant_sample`; no
tensor kernel prototype is emitted.

The constant name list shares the tensor helper prefix and the identical dispatched
header names, so its distinctness, located positions, definition table and literal
pool follow the tensor and scalar development. This is a package-checked product
only: it emits no production artifact, adds no CLI or grammar case, and changes
neither the scalar/tensor renderer nor any existing contract. -/
namespace Rumoca.FMI3.ConstantFunctions
open CTree CMemory CLiteral
open Rumoca.Tensor (Shape)
open Rumoca.ConstantProfile (Decimal)
set_option autoImplicit false
variable {source : AST.Model} {n : Nat}

/-- The declaration-order rate list of the prepared constant-rate model, the
argument the three constant kernel entries carry their literals from. -/
def rates (m : Solve.ConstantFMI3Model n) : List Decimal := List.ofFn m.ivp.rates

/-- The forward declarations of the three constant kernel entries, in the exact
prototypes the emitted kernel functions carry: `rumoca_constant_rhs(double *der)`,
`rumoca_constant_step(double *x)` and `rumoca_constant_sample(double *x, size_t n)`.
No tensor kernel prototype is emitted. -/
def kernelPrototypes (rs : List Decimal) : String :=
  (Rumoca.CConstant.rhsFunction rs).signature.render ++ ";\n" ++
    (Rumoca.CConstant.stepFunction rs).signature.render ++ ";\n" ++
    (Rumoca.CConstant.sampleFunction rs).signature.render ++ ";\n"

/-- The constant adapter declaration preamble: the shared header inclusion block,
the constant-rate instance record layout (no input, no output) and the three
constant kernel entry prototypes. This is the constant analog of
`TensorStorage.declarations`, using the no-input/no-output storage
(`TensorStorage.storageRenderG shape false false`) and the constant kernel
prototypes in place of the tensor kernel/Jacobian prototypes. -/
def declarations (shape : Shape) (rs : List Decimal) : String :=
  Runtime.declarationPrefix ++ TensorStorage.storageRenderG shape false false ++
    kernelPrototypes rs ++ "\n"

/-- Select the emitted constant function body for one pinned header signature. The
shape-dependent behavioral functions dispatch by name; the four constant-specific
ones (`fmi3GetFloat64`, `fmi3SetFloat64`, `fmi3GetContinuousStateDerivatives`,
`fmi3DoStep`) select their proved constant bodies, every other shape-dependent
signature selects the profile-independent tensor body at the constant state shape,
and every remaining signature selects the scalar body `Runtime.function model sig`. -/
def constantDispatch (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sig : Signature) : Function :=
  match sig.name with
  | "fmi3Reset" => TensorReset.function m.shape
  | "fmi3GetNominalsOfContinuousStates" => TensorNominals.function m.shape
  | "fmi3GetNumberOfContinuousStates" => TensorCountQueries.function m.shape false
  | "fmi3GetNumberOfEventIndicators" => TensorCountQueries.function m.shape true
  | "fmi3SetTime" => TensorSetTime.function
  | "fmi3EnterInitializationMode" => TensorLifecycleModes.function .enterInitialization
  | "fmi3ExitInitializationMode" => TensorLifecycleModes.function .exitInitialization
  | "fmi3EnterEventMode" => TensorLifecycleModes.function .enterEvent
  | "fmi3EnterContinuousTimeMode" => TensorLifecycleModes.function .enterContinuous
  | "fmi3Terminate" => TensorLifecycleModes.function .terminate
  | "fmi3FreeInstance" => TensorFree.function
  | "fmi3InstantiateModelExchange" =>
      TensorFactory.function model m.shape .me (TensorMetadata.constantToken m.name)
  | "fmi3InstantiateCoSimulation" =>
      TensorFactory.function model m.shape .cs (TensorMetadata.constantToken m.name)
  | "fmi3GetFloat64" => ConstantFloat64.getFunction m.shape
  | "fmi3SetFloat64" => ConstantFloat64.setFunction m.shape
  | "fmi3GetContinuousStates" => TensorContinuousStates.getFunction m.shape
  | "fmi3SetContinuousStates" => TensorContinuousStates.setFunction m.shape
  | "fmi3GetContinuousStateDerivatives" => ConstantDerivative.derivFunction m.shape
  | "fmi3DoStep" => ConstantDoStep.function
  | _ => Runtime.function model sig

/-- The emitted constant function for one pinned header signature: the dispatched
constant (or tensor, or scalar) body under the exact header prototype `sig`. -/
def constantFunction (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sig : Signature) : Function :=
  { constantDispatch model m sig with signature := sig }

theorem constantFunction_signature (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sig : Signature) : (constantFunction model m sig).signature = sig := rfl

theorem constantFunction_name (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sig : Signature) : (constantFunction model m sig).signature.name = sig.name := rfl

/-- The constant adapter reuses the tensor helper prefix verbatim: the shared
`fail` diagnostic and the two static-factory helpers. -/
abbrev helpers : List CTree.Function := TensorFunctions.helpers

theorem helpers_subset : ∀ fn ∈ helpers, fn ∈ Runtime.helpers := TensorFunctions.helpers_subset

/-- The constant adapter function list: the reused helper prefix followed by one
dispatched constant function per header signature, in header order. -/
def functions (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (signatures : List Signature) : List Function :=
  helpers ++ signatures.map (constantFunction model m)

theorem functions_names (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (signatures : List Signature) :
    (functions model m signatures).map (fun fn => fn.signature.name)
      = helpers.map (fun fn => fn.signature.name) ++ signatures.map (fun sig => sig.name) := by
  simp only [functions, List.map_append]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro sig _
  exact constantFunction_name model m sig

theorem functions_signatures (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (signatures : List Signature) :
    (functions model m signatures).map (fun fn => fn.signature)
      = helpers.map (fun fn => fn.signature) ++ signatures := by
  simp only [functions, List.map_append]
  congr 1
  rw [List.map_map]
  conv_rhs => rw [← List.map_id signatures]
  apply List.map_congr_left
  intro sig _
  exact constantFunction_signature model m sig

/-- The constant adapter names are pairwise distinct whenever the scalar adapter
names are: the name list is the tensor helper prefix (a sublist of the scalar
helpers) followed by the identical dispatched header names. -/
theorem functions_nodup (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (signatures : List Signature)
    (unique : ((LiteralPreparation.functions model signatures).map (fun fn => fn.signature.name)).Nodup) :
    ((functions model m signatures).map (fun fn => fn.signature.name)).Nodup := by
  rw [functions_names]
  rw [TensorFunctions.scalar_names] at unique
  exact (TensorFunctions.helper_names_sublist.append (List.Sublist.refl _)).nodup unique

/-! ### Renderer identity -/

/-- The constant adapter render plan: the model name (fixing the source-link
prefix), the constant declaration preamble, the reused tensor helper prefix and
the per-signature constant body builder. Every render-identity fact for the
constant adapter is an instance of the profile-generic `RenderPlan`
development. -/
def constantPlan (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n) : RenderPlan :=
  planOf TensorInstance.constantProfile m.name (declarations m.shape (rates m))
    helpers (constantFunction model m)

/-- The constant render plan is the constant profile's plan over the model-derived
render inputs: the model name, the constant declaration preamble, the reused
helper prefix and the per-signature constant body builder. -/
theorem constantPlan_planOf (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n) :
    constantPlan model m = planOf TensorInstance.constantProfile m.name
      (declarations m.shape (rates m)) helpers (constantFunction model m) := rfl

/-- The constant adapter render: the fixed preamble (model prefix, `model.c`
include and the constant declaration block) followed by the concatenated helper
and dispatched-function renderings, in header order. -/
def render (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (signatures : List Signature) : String :=
  functionPrefix m.name ++ "#include \"model.c\"\n" ++ declarations m.shape (rates m) ++
    String.join (helpers.map Function.render) ++
    String.join (signatures.map fun sig => (constantFunction model m sig).render)

/-- The constant render is exactly the generic `RenderPlan.render` applied to the
constant render plan; every render-identity fact below is an instance of the
profile-generic development. -/
theorem render_eq_plan (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (signatures : List Signature) :
    render model m signatures = (constantPlan model m).render signatures := rfl

theorem rendered_functions (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (signatures : List Signature) :
    render model m signatures = functionPrefix m.name ++ "#include \"model.c\"\n" ++
      declarations m.shape (rates m) ++ String.join ((functions model m signatures).map Function.render) :=
  (constantPlan model m).rendered_functions signatures

theorem rendered_member (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature) (sig : Signature) (member : sig ∈ sigs) :
    ∃ before after : String,
      render model m sigs = before ++ (constantFunction model m sig).render ++ after :=
  (constantPlan model m).rendered_member sigs sig member

theorem rendered_helper (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature) (fn : Function) (member : fn ∈ helpers) :
    ∃ before after : String, render model m sigs = before ++ fn.render ++ after :=
  (constantPlan model m).rendered_helper sigs fn member

/-! ### Definition table and literal pool -/

/-- The constant adapter definition table: ordinary tree definitions come from the
rendered list; the three constant numerical entries are the constant kernel
functions keyed by their emitted C names. -/
noncomputable def program (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (signatures : List Signature) : CCalls.Program where
  definitions name :=
    match (functions model m signatures).find? (fun fn => fn.signature.name == name) with
    | some fn => some (.tree fn)
    | none => match name with
      | "rumoca_constant_rhs" => some (.tree (Rumoca.CConstant.rhsFunction (rates m)))
      | "rumoca_constant_step" => some (.tree (Rumoca.CConstant.stepFunction (rates m)))
      | "rumoca_constant_sample" => some (.tree (Rumoca.CConstant.sampleFunction (rates m)))
      | _ => none
  kernel := CSyntax.fromTarget (C.lower model.solve)

private theorem find_function (funcs : List Function) (fn : Function)
    (unique : (funcs.map (fun f => f.signature.name)).Nodup)
    (member : fn ∈ funcs) :
    funcs.find? (fun f => f.signature.name == fn.signature.name) = some fn := by
  induction funcs with
  | nil => contradiction
  | cons head rest ih =>
      simp only [List.map_cons, List.nodup_cons] at unique
      rcases List.mem_cons.mp member with rfl | member
      · simp
      · have different : head.signature.name ≠ fn.signature.name := by
          intro same
          exact unique.1 (List.mem_map.mpr ⟨fn, member, same.symm⟩)
        simpa [different] using ih unique.2 member

theorem definition_bound (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (signatures : List Signature)
    (unique : ((functions model m signatures).map (fun fn => fn.signature.name)).Nodup)
    (fn : Function) (member : fn ∈ functions model m signatures) :
    (program model m signatures).definitions fn.signature.name = some (.tree fn) := by
  have found := find_function (functions model m signatures) fn unique member
  simp only [program, found]

theorem function_bound (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (signatures : List Signature)
    (unique : ((functions model m signatures).map (fun fn => fn.signature.name)).Nodup)
    (sig : Signature) (member : sig ∈ signatures) :
    (program model m signatures).definitions sig.name
      = some (.tree (constantFunction model m sig)) := by
  have bound := definition_bound model m signatures unique (constantFunction model m sig)
    (List.mem_append_right _ (List.mem_map.mpr ⟨sig, member, rfl⟩))
  rwa [constantFunction_name] at bound

/-- Every listed function of the constant adapter is bound to itself as a tree in
the definition table; a listed `.tree` definition whose name matches a function is
that function. -/
theorem program_covered (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (signatures : List Signature) (name : String) (fn : Function)
    (found : (functions model m signatures).find? (fun fn => fn.signature.name == name) = some fn) :
    (program model m signatures).definitions name = some (.tree fn) := by
  simp only [program, found]

/-- The reused `fail` helper (and every reused helper) is bound to its rendered
tree in the constant definition table. -/
theorem helpers_bound (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (signatures : List Signature) (fn : Function) (member : fn ∈ helpers) :
    (program model m signatures).definitions fn.signature.name = some (.tree fn) := by
  simp only [helpers, TensorFunctions.helpers, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> rfl

def prepare (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (signatures : List Signature) :
    Option (Pool (LiteralPreparation.excluded ++ (functions model m signatures).flatMap functionNames)) :=
  Pool.forFunctions LiteralPreparation.excluded (functions model m signatures)

theorem header_fresh (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (signatures : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++ (functions model m signatures).flatMap functionNames)) :
    pool.HeaderFresh cInterface := by
  apply pool.headerFresh_of_reserved
  intro name value found
  exact List.mem_append_left _ (LiteralPreparation.constants_covered name value found)

theorem text_bound (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (signatures : List Signature)
    {pool : Pool (LiteralPreparation.excluded ++ (functions model m signatures).flatMap functionNames)}
    (made : prepare model m signatures = some pool) (fn : Function)
    (member : fn ∈ functions model m signatures) (text : String)
    (occurs : text ∈ functionTexts fn) (firstBlock : Nat) :
    ∃ address, pool.addresses firstBlock text = some address := by
  have occurrence : ∃ fn ∈ functions model m signatures, text ∈ functionTexts fn := ⟨fn, member, occurs⟩
  obtain ⟨name, named⟩ := (Pool.forFunctions_coverage made).mpr occurrence
  simp only [Pool.symbols, Option.map_eq_some_iff] at named
  obtain ⟨entry, found, rfl⟩ := named
  exact ⟨entry.address firstBlock, by simp [Pool.addresses, found]⟩

theorem pool_complete (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (signatures : List Signature)
    {pool : Pool (LiteralPreparation.excluded ++ (functions model m signatures).flatMap functionNames)}
    (made : prepare model m signatures = some pool) :
    ∀ fn ∈ functions model m signatures, functionTexts (Lowering.function pool.symbols fn) = [] :=
  fun _ member => Pool.forFunctions_complete made member

/-! ### Call resolution for the prepared constant kernel entries -/

/-- The constant kernel entry `rumoca_constant_rhs` always resolves in the constant
definition table. -/
theorem kernel_entry_resolves (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (signatures : List Signature) :
    ((program model m signatures).definitions "rumoca_constant_rhs").isSome := by
  simp only [program]
  cases (functions model m signatures).find? (fun fn => fn.signature.name == "rumoca_constant_rhs") <;>
    simp

/-- No listed function of the constant adapter carries a name reserved for a
constant kernel entry, given the header signatures avoid those names. -/
private theorem find_kernel_none (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (signatures : List Signature) (kname : String)
    (helperNe : ∀ fn ∈ helpers, ¬ (fn.signature.name == kname) = true)
    (fresh : ∀ sig ∈ signatures, sig.name ≠ kname) :
    (functions model m signatures).find? (fun fn => fn.signature.name == kname) = none := by
  rw [List.find?_eq_none]
  intro fn member
  rcases List.mem_append.mp member with helper | exported
  · exact helperNe fn helper
  · obtain ⟨sig, sigMember, rfl⟩ := List.mem_map.mp exported
    rw [constantFunction_name]; simp only [beq_iff_eq]; exact fresh sig sigMember

/-- The constant derivative kernel entry `rumoca_constant_rhs` resolves specifically
to its bound tree, the same function `ConstantInstanceRhs.kernelDefinitions` names,
when no listed header signature shadows the name. -/
theorem kernel_entry_rhs (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (signatures : List Signature) (fresh : ∀ sig ∈ signatures, sig.name ≠ "rumoca_constant_rhs") :
    (program model m signatures).definitions "rumoca_constant_rhs"
      = some (.tree (Rumoca.CConstant.rhsFunction (rates m))) := by
  have none := find_kernel_none model m signatures "rumoca_constant_rhs"
    (by intro fn member; simp only [helpers, TensorFunctions.helpers, List.mem_cons,
      List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl <;> decide) fresh
  simp only [program, none]

/-- The constant step kernel entry `rumoca_constant_step` resolves specifically to
its bound tree when no listed header signature shadows the name. -/
theorem kernel_entry_step (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (signatures : List Signature) (fresh : ∀ sig ∈ signatures, sig.name ≠ "rumoca_constant_step") :
    (program model m signatures).definitions "rumoca_constant_step"
      = some (.tree (Rumoca.CConstant.stepFunction (rates m))) := by
  have none := find_kernel_none model m signatures "rumoca_constant_step"
    (by intro fn member; simp only [helpers, TensorFunctions.helpers, List.mem_cons,
      List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl <;> decide) fresh
  simp only [program, none]

/-- The constant sample kernel entry `rumoca_constant_sample` resolves specifically
to its bound tree when no listed header signature shadows the name. -/
theorem kernel_entry_sample (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (signatures : List Signature) (fresh : ∀ sig ∈ signatures, sig.name ≠ "rumoca_constant_sample") :
    (program model m signatures).definitions "rumoca_constant_sample"
      = some (.tree (Rumoca.CConstant.sampleFunction (rates m))) := by
  have none := find_kernel_none model m signatures "rumoca_constant_sample"
    (by intro fn member; simp only [helpers, TensorFunctions.helpers, List.mem_cons,
      List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl <;> decide) fresh
  simp only [program, none]

/-- The three resolved constant kernel entries are exactly the trees
`ConstantInstanceRhs.kernelDefinitions` names, so those constant kernel definitions
extend the constant definition table when the header signatures avoid the entry
names. This is the constant analog of the tensor kernel-entry resolution. -/
theorem program_extends_kernel (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (signatures : List Signature)
    (freshRhs : ∀ sig ∈ signatures, sig.name ≠ "rumoca_constant_rhs")
    (freshStep : ∀ sig ∈ signatures, sig.name ≠ "rumoca_constant_step")
    (freshSample : ∀ sig ∈ signatures, sig.name ≠ "rumoca_constant_sample") :
    CCalls.Typed.Extends (ConstantInstanceRhs.kernelDefinitions (rates m)) (program model m signatures) := by
  intro name fn found
  simp only [ConstantInstanceRhs.kernelDefinitions] at found
  split at found
  · rename_i h; subst h; simp only [Option.some.injEq] at found; subst found
    exact kernel_entry_rhs model m signatures freshRhs
  · split at found
    · rename_i h; subst h; simp only [Option.some.injEq] at found; subst found
      exact kernel_entry_step model m signatures freshStep
    · split at found
      · rename_i h; subst h; simp only [Option.some.injEq] at found; subst found
        exact kernel_entry_sample model m signatures freshSample
      · simp at found

/-- The prototype of the constant derivative kernel entry agrees with the arguments
the constant derivative getter passes: its parameter list has the same length as
`ConstantDerivative.entryArgs` (the single written derivative region), and its
declared parameter name is the entry's own `der`. -/
theorem rhs_prototype_matches_args (rs : List Decimal) :
    (Rumoca.CConstant.rhsFunction rs).signature.parameters.length =
        ConstantDerivative.entryArgs.length ∧
      (Rumoca.CConstant.rhsFunction rs).signature.parameters.map CTree.Parameter.name = ["der"] :=
  ⟨rfl, rfl⟩

/-- The prototype of the constant step kernel entry agrees with the single state
region pointer the constant `fmi3DoStep` numerical tail passes to
`rumoca_constant_step`. -/
theorem step_prototype_matches_args (rs : List Decimal) :
    (Rumoca.CConstant.stepFunction rs).signature.parameters.length = 1 ∧
      (Rumoca.CConstant.stepFunction rs).signature.parameters.map CTree.Parameter.name = ["x"] :=
  ⟨rfl, rfl⟩

end Rumoca.FMI3.ConstantFunctions
