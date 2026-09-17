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
import RumocaFMI3.TensorMetadata

/-! The tensor FMI 3 adapter function list. This is the tensor analog of
`LiteralPreparation.functions`: each pinned header signature renders either its
proved tensor behavioral body (19 shape-dependent functions dispatched by name)
or, for every model-independent behavioral and unsupported/absent-type function,
the same body the scalar renderer emits (`Runtime.function model sig`). The
tensor helper prefix (`TensorFunctions.helpers`) reuses the shared `fail`
diagnostic and the two static-factory helpers, dropping the scalar
`model_rhs`/`model_advance` wrappers, which are dead for the tensor bodies. The
declaration preamble is the tensor storage preamble (`TensorStorage.declarations`):
the shared header inclusion block, the tensor instance record layout the tensor
bodies address (in place of the scalar instance record), and the forward
declaration of the prepared kernel entry the bodies call directly.

The tensor name list is a sublist of the scalar list's (the shared helper prefix
minus the two dead wrappers, then the identical dispatched header names), so its
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

/-- Select the emitted tensor function body for one pinned header signature. The
19 shape-dependent behavioral functions dispatch by name to their proved tensor
bodies; every other signature (the seven model-independent behavioral functions
and the 49 unsupported/absent-type functions) selects the scalar body
`Runtime.function model sig`. The signature this body is paired with is fixed by
`tensorFunction` to the header prototype `sig`, so a dispatched body whose own
reduced prototype carries fewer parameters than the header (the Model Exchange
`fmi3EnterInitializationMode`) is emitted under the full header prototype, with
the extra parameters unused by the body. -/
def tensorDispatch (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
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
  | "fmi3InstantiateModelExchange" => TensorFactory.function model shape .me (TensorMetadata.token m)
  | "fmi3InstantiateCoSimulation" => TensorFactory.function model shape .cs (TensorMetadata.token m)
  | "fmi3GetFloat64" => TensorFloat64.getFunction shape (outputShape m)
  | "fmi3SetFloat64" => TensorFloat64.setFunction shape
  | "fmi3GetContinuousStates" => TensorContinuousStates.getFunction shape
  | "fmi3SetContinuousStates" => TensorContinuousStates.setFunction shape
  | "fmi3GetContinuousStateDerivatives" => TensorContinuousStates.derivFunction shape
  | "fmi3DoStep" => TensorDoStep.function shape
  | _ => Runtime.function model sig

/-- The emitted tensor function for one pinned header signature: the dispatched
tensor (or scalar) body under the exact header prototype `sig`. Pairing the body
with the header signature makes every emitted function conform to the pinned
prototype for its name; parameters a body ignores are simply unused. -/
def tensorFunction (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sig : Signature) : Function :=
  { tensorDispatch model m sig with signature := sig }

/-- Every emitted tensor function carries exactly the pinned header prototype for
its name; in particular its signature name is the header name. -/
theorem tensorFunction_signature (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sig : Signature) : (tensorFunction model m sig).signature = sig := rfl

theorem tensorFunction_name (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sig : Signature) : (tensorFunction model m sig).signature.name = sig.name := rfl

/-- The tensor adapter helper prefix: the shared `fail` diagnostic
(`Runtime.helpers[0]`) and the two static-factory helpers the tensor factory
bodies call (`rumoca_valid_identity`, `rumoca_reserve_slot`). The scalar
`model_rhs`/`model_advance` wrappers are dropped: the tensor bodies call the
prepared kernel entry `rumoca_rhs` directly (forward-declared in the preamble by
`TensorStorage.kernelPrototype`), so those scalar wrappers over the scalar `Model`
record are dead for the tensor adapter. -/
def helpers : List CTree.Function :=
  [Runtime.helpers[0], Identity.function, CAtomicScan.function]

/-- Each tensor helper is one of the shared scalar helpers, so its printability
and every shared helper fact carries over. -/
theorem helpers_subset : ∀ fn ∈ helpers, fn ∈ Runtime.helpers := by
  intro fn member
  simp only [helpers, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp [Runtime.helpers]

/-- The tensor adapter function list: the tensor helper prefix followed by one
dispatched tensor function per header signature, in header order. -/
def functions (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature) : List Function :=
  helpers ++ signatures.map (tensorFunction model m)

/-- The tensor adapter public-name list: the tensor helper names followed by the
dispatched header names (each dispatched function keeps its header name). -/
theorem functions_names (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature) :
    (functions model m signatures).map (fun fn => fn.signature.name)
      = helpers.map (fun fn => fn.signature.name) ++ signatures.map (fun sig => sig.name) := by
  simp only [functions, List.map_append]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro sig _
  exact tensorFunction_name model m sig

/-- The tensor adapter signature list equals the header signature list position by
position, after the fixed tensor helper prefix: every dispatched tensor function
is emitted under the exact pinned header prototype at its list slot, not merely
under a matching name. This is the prototype-level strengthening of
`functions_names`. -/
theorem functions_signatures (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature) :
    (functions model m signatures).map (fun fn => fn.signature)
      = helpers.map (fun fn => fn.signature) ++ signatures := by
  simp only [functions, List.map_append]
  congr 1
  rw [List.map_map]
  conv_rhs => rw [← List.map_id signatures]
  apply List.map_congr_left
  intro sig _
  exact tensorFunction_signature model m sig

/-- The scalar adapter public-name list is the scalar helper names followed by the
same dispatched header names; the two lists differ only in their helper prefix. -/
theorem scalar_names (model : Solve.FMI3Model source) (signatures : List Signature) :
    (LiteralPreparation.functions model signatures).map (fun fn => fn.signature.name)
      = Runtime.helpers.map (fun fn => fn.signature.name) ++ signatures.map (fun sig => sig.name) := by
  simp only [LiteralPreparation.functions, List.map_append]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro sig _
  rfl

/-- The tensor helper names are a sublist of the scalar helper names: the tensor
prefix drops the two dead scalar wrappers `model_rhs`/`model_advance`. -/
theorem helper_names_sublist :
    (helpers.map (fun fn => fn.signature.name)).Sublist
      (Runtime.helpers.map (fun fn => fn.signature.name)) := by
  decide +kernel

/-- The tensor adapter names are pairwise distinct whenever the scalar adapter
names are: the tensor name list is a sublist of the scalar one (the shared helper
prefix minus the two dead scalar wrappers, then the identical dispatched header
names), and `Nodup` is closed under sublists. -/
theorem functions_nodup (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature)
    (unique : ((LiteralPreparation.functions model signatures).map (fun fn => fn.signature.name)).Nodup) :
    ((functions model m signatures).map (fun fn => fn.signature.name)).Nodup := by
  rw [functions_names]
  rw [scalar_names] at unique
  exact (helper_names_sublist.append (List.Sublist.refl _)).nodup unique

/-! ### Renderer identity -/

/-- The tensor adapter render: the fixed preamble (model prefix, `model.c`
include and the shared declaration block) followed by the concatenated helper
and dispatched-function renderings, in header order. -/
def render (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature) : String :=
  functionPrefix m.name ++ "#include \"model.c\"\n" ++ TensorStorage.declarations shape m.hasOutput ++
    String.join (helpers.map Function.render) ++
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
    String.join (helpers.map Function.render) ++
    String.join (left.map fun sig => (tensorFunction model m sig).render),
    String.join (right.map fun sig => (tensorFunction model m sig).render), ?_⟩
  apply String.toList_injective
  simp [render, String.toList_append, CString.join_toList,
    List.flatMap_map, List.append_assoc]

/-- Every helper is a concrete fragment of the same emitted function list. -/
theorem rendered_helper (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List Signature) (fn : Function) (member : fn ∈ helpers) :
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

/-- The reused `fail` helper (and every tensor helper) is bound to its rendered
tree in the tensor definition table. -/
theorem helpers_bound (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature) (fn : Function) (member : fn ∈ helpers) :
    (program model m signatures).definitions fn.signature.name = some (.tree fn) := by
  simp only [helpers, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> rfl

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

/-! ### Call resolution for the prepared kernel entry

The tensor bodies call the prepared derivative kernel `rumoca_rhs` directly by
name (`TensorContinuousStates.derivEntryArgs`, `TensorDoStep`), rather than
through a scalar `model_rhs` wrapper over the scalar `Model` record. These facts
show the direct call resolves in the tensor definition table and that the
preamble prototype `TensorStorage.kernelPrototype` agrees with the arguments the
bodies pass. The shared helpers the bodies call (`fail`,
`rumoca_valid_identity`, `rumoca_reserve_slot`) resolve through `helpers_bound`. -/

/-- The prepared kernel entry `rumoca_rhs` always resolves in the tensor
definition table: it is defined either as a listed tree (if some header signature
shadowed the name) or, otherwise, as the prepared RHS kernel declared in the
preamble. It is never unresolved. -/
theorem kernel_entry_resolves (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature) :
    ((program model m signatures).definitions "rumoca_rhs").isSome := by
  simp only [program]
  cases (functions model m signatures).find? (fun fn => fn.signature.name == "rumoca_rhs") <;>
    simp

/-- When no listed signature is named `rumoca_rhs` (the pinned FMI header names
all start with `fmi3`, disjoint from the kernel entry names), the direct call
resolves specifically to the prepared RHS kernel declared in the preamble. -/
theorem kernel_entry_is_kernel (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (signatures : List Signature) (fresh : ∀ sig ∈ signatures, sig.name ≠ "rumoca_rhs") :
    (program model m signatures).definitions "rumoca_rhs" = some (.kernel .rhs) := by
  have none : (functions model m signatures).find? (fun fn => fn.signature.name == "rumoca_rhs")
      = none := by
    rw [List.find?_eq_none]
    intro fn member
    rcases List.mem_append.mp member with helper | exported
    · simp only [helpers, List.mem_cons, List.not_mem_nil, or_false] at helper
      rcases helper with rfl | rfl | rfl <;> decide
    · obtain ⟨sig, sigMember, rfl⟩ := List.mem_map.mp exported
      rw [tensorFunction_name]
      simp only [beq_iff_eq]
      exact fresh sig sigMember
  simp only [program, none]

/-- The preamble prototype of the kernel entry agrees with the arguments the
tensor bodies pass: its parameter list has the same length as
`TensorContinuousStates.derivEntryArgs` (the three region pointers and the
element count), and its parameter names are exactly the instance fields the
derivative arguments address, in order. -/
theorem kernel_prototype_matches_args :
    TensorStorage.kernelSignature.parameters.length =
        TensorContinuousStates.derivEntryArgs.length ∧
      TensorStorage.kernelSignature.parameters.map CTree.Parameter.name =
        [TensorInstance.stateName, TensorInstance.inputName,
          TensorInstance.derivativeName, "count"] :=
  ⟨rfl, rfl⟩

end Rumoca.FMI3.TensorFunctions
