import RumocaFMI3.LiteralPreparation
import RumocaFMI3.TensorReset
import RumocaFMI3.TensorNominals
import RumocaFMI3.TensorCountQueries
import RumocaFMI3.TensorSetTime
import RumocaFMI3.TensorLifecycleModes
import RumocaFMI3.TensorFree
import RumocaFMI3.TensorStaticFactory
import RumocaFMI3.TensorFloat64Access
import RumocaFMI3.TensorContinuousStates
import RumocaFMI3.TensorDoStep
import RumocaFMI3.TensorStorageCode

/-! The tensor FMI 3 adapter function list. This is the tensor analog of
`LiteralPreparation.functions`: each pinned header signature renders either its
proved tensor behavioral body (19 shape-dependent functions dispatched by name)
or, for every model-independent behavioral and unsupported/absent-type function,
the same body the scalar renderer emits (`Runtime.function model sig`). The
shared helper prefix (`Runtime.helpers`, including the `fail` diagnostic the
family failure paths call) is reused verbatim. The declaration preamble is the
tensor storage preamble (`TensorStorage.declarations`): the shared header
inclusion block followed by the tensor instance record layout the tensor bodies
address, in place of the scalar instance record.

The name multiset of this list equals the scalar list's name multiset, so its
distinctness, located positions, definition table and literal pool follow the
scalar development. This is a package-checked product only: it emits no
production artifact, adds no CLI or grammar case, and changes neither the scalar
renderer nor any existing contract. The scalar model witness supplies the fixed
model-independent bodies and the numerical kernel; tensor rank and extents stay
symbolic in the shape parameter. -/
namespace Rumoca.FMI3.TensorFunctions
open CTree CMemory CLiteral
open Rumoca.Tensor (Shape matrixShape)
set_option autoImplicit false
variable {source : AST.Model} {shape : Shape}

/-- The optional dense (Jacobian) observation shape carried by the getter for
`fmi3GetFloat64`: a square matrix over the state element count when the prepared
problem exposes a dense output, otherwise absent. -/
def outputShape (m : Solve.TensorFMI3Model shape) : Option Shape :=
  m.ivp.diagonal.map (fun _ => matrixShape shape.volume shape.volume)

/-- Map one pinned header signature to its emitted tensor function. The 19
shape-dependent behavioral functions dispatch by name to their proved tensor
bodies; every other signature (the seven model-independent behavioral functions
and the 49 unsupported/absent-type functions) renders exactly the scalar body
`Runtime.function model sig`. -/
def tensorFunction (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sig : Signature) : Function :=
  match sig.name with
  | "fmi3Reset" => TensorReset.function shape
  | "fmi3GetNominalsOfContinuousStates" => TensorNominals.function shape
  | "fmi3GetNumberOfContinuousStates" => TensorCountQueries.function shape false
  | "fmi3GetNumberOfEventIndicators" => TensorCountQueries.function shape true
  | "fmi3SetTime" => TensorSetTime.function
  | "fmi3EnterInitializationMode" => TensorLifecycleModes.function .enterInitialization
  | "fmi3ExitInitializationMode" => TensorLifecycleModes.function .exitInitialization
  | "fmi3EnterEventMode" => TensorLifecycleModes.function .enterEvent
  | "fmi3EnterContinuousTimeMode" => TensorLifecycleModes.function .enterContinuous
  | "fmi3Terminate" => TensorLifecycleModes.function .terminate
  | "fmi3FreeInstance" => TensorFree.function
  | "fmi3InstantiateModelExchange" => TensorFactory.function model shape .me
  | "fmi3InstantiateCoSimulation" => TensorFactory.function model shape .cs
  | "fmi3GetFloat64" => TensorFloat64.getFunction shape (outputShape m)
  | "fmi3SetFloat64" => TensorFloat64.setFunction shape
  | "fmi3GetContinuousStates" => TensorContinuousStates.getFunction shape
  | "fmi3SetContinuousStates" => TensorContinuousStates.setFunction shape
  | "fmi3GetContinuousStateDerivatives" => TensorContinuousStates.derivFunction shape
  | "fmi3DoStep" => TensorDoStep.function shape
  | _ => Runtime.function model sig

/-- Every dispatched tensor function keeps the header signature's name; the
behavioral bodies name the same public function, and the fallthrough is the
scalar body over the same signature. -/
theorem tensorFunction_name (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sig : Signature) : (tensorFunction model m sig).signature.name = sig.name := by
  unfold tensorFunction
  split <;>
    simp_all only [reduceIte, Bool.false_eq_true, if_true, if_false,
      TensorReset.function, TensorReset.signature, TensorNominals.function,
      TensorNominals.signature, ErrorCalls.nominalSignature, TensorCountQueries.function,
      TensorCountQueries.signature, TensorSetTime.function, TensorSetTime.signature,
      TensorLifecycleModes.function, TensorLifecycleModes.signature, TensorLifecycleModes.Phase.name,
      TensorFree.function, StaticRelease.function, TensorFactory.function, FactoryArguments.signature,
      Identity.factoryName, TensorFloat64.getFunction, TensorFloat64.setFunction, Float64Calls.signature,
      TensorContinuousStates.getFunction, TensorContinuousStates.setFunction,
      TensorContinuousStates.derivFunction, TensorContinuousStates.signature, DerivativeCalls.signature,
      TensorDoStep.function, TensorDoStep.signature, Runtime.function]

/-- The tensor adapter function list: the reused helper prefix followed by one
dispatched tensor function per header signature, in header order. -/
def functions (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature) : List Function :=
  Runtime.helpers ++ signatures.map (tensorFunction model m)

/-- The tensor adapter list and the scalar adapter list have the same name
multiset: the helper prefix is shared and each dispatched tensor function keeps
its header name. -/
theorem functions_names (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature) :
    (functions model m signatures).map (fun fn => fn.signature.name)
      = (LiteralPreparation.functions model signatures).map (fun fn => fn.signature.name) := by
  simp only [functions, LiteralPreparation.functions, List.map_append]
  congr 1
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro sig _
  exact tensorFunction_name model m sig

/-- The tensor adapter names are pairwise distinct whenever the scalar adapter
names are, universally in the shape and the scalar model witness. -/
theorem functions_nodup (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature)
    (unique : ((LiteralPreparation.functions model signatures).map (fun fn => fn.signature.name)).Nodup) :
    ((functions model m signatures).map (fun fn => fn.signature.name)).Nodup := by
  rw [functions_names]; exact unique

/-! ### Renderer identity -/

/-- The tensor adapter render: the fixed preamble (model prefix, `model.c`
include and the shared declaration block) followed by the concatenated helper
and dispatched-function renderings, in header order. -/
def render (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature) : String :=
  functionPrefix m.name ++ "#include \"model.c\"\n" ++ TensorStorage.declarations shape m.hasOutput ++
    String.join (Runtime.helpers.map Function.render) ++
    String.join (signatures.map fun sig => (tensorFunction model m sig).render)

theorem rendered_functions (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature) :
    render model m signatures = functionPrefix m.name ++ "#include \"model.c\"\n" ++
      TensorStorage.declarations shape m.hasOutput ++ String.join ((functions model m signatures).map Function.render) := by
  apply String.toList_injective
  simp [render, functions, String.toList_append, CString.join_toList,
    List.flatMap_map, List.append_assoc]

/-- Each header signature is rendered exactly once at its actual list slot. -/
theorem rendered_member (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List Signature) (sig : Signature) (member : sig ∈ sigs) :
    ∃ before after : String,
      render model m sigs = before ++ (tensorFunction model m sig).render ++ after := by
  obtain ⟨left, right, rfl⟩ := List.mem_iff_append.mp member
  refine ⟨functionPrefix m.name ++ "#include \"model.c\"\n" ++ TensorStorage.declarations shape m.hasOutput ++
    String.join (Runtime.helpers.map Function.render) ++
    String.join (left.map fun sig => (tensorFunction model m sig).render),
    String.join (right.map fun sig => (tensorFunction model m sig).render), ?_⟩
  apply String.toList_injective
  simp [render, String.toList_append, CString.join_toList,
    List.flatMap_map, List.append_assoc]

/-- Every helper is a concrete fragment of the same emitted function list. -/
theorem rendered_helper (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List Signature) (fn : Function) (member : fn ∈ Runtime.helpers) :
    ∃ before after : String, render model m sigs = before ++ fn.render ++ after := by
  obtain ⟨left, right, same⟩ := List.mem_iff_append.mp member
  refine ⟨functionPrefix m.name ++ "#include \"model.c\"\n" ++ TensorStorage.declarations shape m.hasOutput ++
    String.join (left.map Function.render),
    String.join (right.map Function.render) ++
      String.join (sigs.map fun sig => (tensorFunction model m sig).render), ?_⟩
  apply String.toList_injective
  simp [render, same, String.toList_append, CString.join_toList,
    List.flatMap_map, List.append_assoc]

/-! ### Definition table and literal pool -/

/-- The tensor adapter definition table, mirroring the scalar one: ordinary tree
definitions come from the rendered list; the three numerical entries use the
prepared Solve kernel of the scalar witness model. -/
noncomputable def program (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature) : CCalls.Program where
  definitions name :=
    match (functions model m signatures).find? (fun fn => fn.signature.name == name) with
    | some fn => some (.tree fn)
    | none => match name with
      | "rumoca_rhs" => some (.kernel .rhs)
      | "rumoca_step" => some (.kernel .step)
      | "rumoca_sample" => some (.kernel .sample)
      | _ => none
  kernel := CSyntax.fromTarget (C.lower model.solve)

private theorem find_function (functions : List Function) (fn : Function)
    (unique : (functions.map (fun f => f.signature.name)).Nodup)
    (member : fn ∈ functions) :
    functions.find? (fun f => f.signature.name == fn.signature.name) = some fn := by
  induction functions with
  | nil => contradiction
  | cons head rest ih =>
      simp only [List.map_cons, List.nodup_cons] at unique
      rcases List.mem_cons.mp member with rfl | member
      · simp
      · have different : head.signature.name ≠ fn.signature.name := by
          intro same
          exact unique.1 (List.mem_map.mpr ⟨fn, member, same.symm⟩)
        simpa [different] using ih unique.2 member

theorem definition_bound (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature)
    (unique : ((functions model m signatures).map (fun fn => fn.signature.name)).Nodup)
    (fn : Function) (member : fn ∈ functions model m signatures) :
    (program model m signatures).definitions fn.signature.name = some (.tree fn) := by
  have found := find_function (functions model m signatures) fn unique member
  simp only [program, found]

theorem function_bound (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature)
    (unique : ((functions model m signatures).map (fun fn => fn.signature.name)).Nodup)
    (sig : Signature) (member : sig ∈ signatures) :
    (program model m signatures).definitions sig.name
      = some (.tree (tensorFunction model m sig)) := by
  have bound := definition_bound model m signatures unique (tensorFunction model m sig)
    (List.mem_append_right _ (List.mem_map.mpr ⟨sig, member, rfl⟩))
  rwa [tensorFunction_name] at bound

theorem program_covered (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature) (name : String) (fn : Function)
    (defined : (program model m signatures).definitions name = some (.tree fn)) :
    fn ∈ functions model m signatures := by
  unfold program at defined
  cases found : (functions model m signatures).find? (fun fn => fn.signature.name == name) with
  | none =>
      simp only [found] at defined
      split at defined <;> simp at defined
  | some tree =>
      simp only [found, Option.some.injEq, CCalls.Definition.tree.injEq] at defined
      subst tree
      exact List.mem_of_find?_eq_some found

/-- The reused `fail` helper (and every helper) is bound to its rendered tree. -/
theorem helpers_bound (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature) (fn : Function) (member : fn ∈ Runtime.helpers) :
    (program model m signatures).definitions fn.signature.name = some (.tree fn) := by
  simp [Runtime.helpers] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> rfl

def prepare (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature) :
    Option (Pool (LiteralPreparation.excluded ++ (functions model m signatures).flatMap functionNames)) :=
  Pool.forFunctions LiteralPreparation.excluded (functions model m signatures)

theorem header_fresh (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++ (functions model m signatures).flatMap functionNames)) :
    pool.HeaderFresh cInterface := by
  apply pool.headerFresh_of_reserved
  intro name value found
  exact List.mem_append_left _ (LiteralPreparation.constants_covered name value found)

/-- Every collected occurrence has a constructed address. -/
theorem text_bound (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
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

theorem pool_complete (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature)
    {pool : Pool (LiteralPreparation.excluded ++ (functions model m signatures).flatMap functionNames)}
    (made : prepare model m signatures = some pool) :
    ∀ fn ∈ functions model m signatures, functionTexts (Lowering.function pool.symbols fn) = [] :=
  fun _ member => Pool.forFunctions_complete made member

end Rumoca.FMI3.TensorFunctions
