import RumocaFMI3.Runtime
import RumocaFMI3.CInterface
import RumocaC.LiteralCollection
import RumocaC.LiteralNames
import RumocaC.LiteralDeclarationBlock

/-! Bind literal collection and the authored definition table to the function
list used by the actual FMI adapter renderer. This preparation does not change
production output or certify native headers, function pointers or allocation. -/
namespace Rumoca.FMI3.LiteralPreparation
open CTree CMemory CLiteral
set_option autoImplicit false
variable {source : AST.Model}

def functions (m : Solve.FMI3Model source) (signatures : List Signature) : List Function :=
  Runtime.helpers ++ signatures.map (Runtime.function m)

theorem rendered_functions (m : Solve.FMI3Model source) (signatures : List Signature) :
    Runtime.render m signatures = functionPrefix m.name ++ "#include \"model.c\"\n" ++
      Runtime.declarations ++ String.join ((functions m signatures).map Function.render) := by
  apply String.toList_injective
  simp [Runtime.render, functions, String.toList_append, CString.join_toList,
    List.flatMap_map, List.append_assoc]

/-- Constants interpreted by the authored FMI C interface. This is not the
complete macro/typedef namespace of an implementation's standard headers. -/
def excluded : List String :=
  ["fmi3OK", "fmi3Warning", "fmi3Discard", "fmi3Error", "fmi3Fatal", "NULL"]

theorem constants_covered (name : String) (value : Value)
    (found : cConstants name = some value) : name ∈ excluded := by
  unfold cConstants at found
  split at found <;> simp_all [excluded]

def prepare (m : Solve.FMI3Model source) (signatures : List Signature) :
    Option (Pool (excluded ++ (functions m signatures).flatMap functionNames)) :=
  Pool.forFunctions excluded (functions m signatures)

theorem header_fresh (m : Solve.FMI3Model source) (signatures : List Signature)
    (pool : Pool (excluded ++ (functions m signatures).flatMap functionNames)) :
    pool.HeaderFresh cInterface := by
  apply pool.headerFresh_of_reserved
  intro name value found
  exact List.mem_append_left _ (constants_covered name value found)

/-- Ordinary tree definitions come from the rendered list; the three existing
numerical functions use the prepared Solve kernel. Missing externals remain
unsupported, rather than acquiring name-specific successful results. -/
noncomputable def program (m : Solve.FMI3Model source) (signatures : List Signature) : CCalls.Program where
  definitions name :=
    match (functions m signatures).find? (fun fn => fn.signature.name == name) with
    | some fn => some (.tree fn)
    | none => match name with
      | "rumoca_rhs" => some (.kernel .rhs)
      | "rumoca_step" => some (.kernel .step)
      | "rumoca_sample" => some (.kernel .sample)
      | _ => none
  kernel := CSyntax.fromTarget (C.lower m.solve)

theorem program_covered (m : Solve.FMI3Model source) (signatures : List Signature)
    (name : String) (fn : Function)
    (defined : (program m signatures).definitions name = some (.tree fn)) :
    fn ∈ functions m signatures := by
  unfold program at defined
  cases found : (functions m signatures).find? (fun fn => fn.signature.name == name) with
  | none =>
      simp only [found] at defined
      split at defined <;> simp at defined
  | some tree =>
      simp only [found, Option.some.injEq, CCalls.Definition.tree.injEq] at defined
      subst tree
      exact List.mem_of_find?_eq_some found

/-- Existing helper-call proofs can use this constructed binding instead of
an arbitrary definition-table premise. The table and renderer share order. -/
theorem helpers_bound (m : Solve.FMI3Model source) (signatures : List Signature)
    (fn : Function) (member : fn ∈ Runtime.helpers) :
    (program m signatures).definitions fn.signature.name = some (.tree fn) := by
  simp [Runtime.helpers] at member
  rcases member with rfl | rfl | rfl <;> rfl

theorem pool_complete (m : Solve.FMI3Model source) (signatures : List Signature)
    {pool : Pool (excluded ++ (functions m signatures).flatMap functionNames)}
    (made : prepare m signatures = some pool) :
    ∀ fn ∈ functions m signatures, functionTexts (Lowering.function pool.symbols fn) = [] :=
  fun _ member => Pool.forFunctions_complete made member

theorem declarations_correct (m : Solve.FMI3Model source) (signatures : List Signature)
    (pool : Pool (excluded ++ (functions m signatures).flatMap functionNames)) :
    Declaration.BlockCorrect ("isfinite" :: excluded ++ (functions m signatures).flatMap functionNames)
      pool.entries (Declaration.renderBlock pool.entries).toList :=
  Declaration.renderBlock_correct pool.entries (fun _ member => (pool.entry_valid member).1)

macro "fmi_literal_calls" : tactic => `(tactic|
  simp [CLiteral.Lowering.CallsWellFormed, CLiteral.Lowering.CallHeadSafe,
    Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.reject,
    Runtime.fail, Runtime.branch, Runtime.ret, Runtime.v, Runtime.n,
    Runtime.call, Runtime.log, Runtime.ok, Runtime.put, Runtime.setMode,
    Runtime.out, Runtime.scalarAccessCheck, Runtime.countLoop, Runtime.pointerCheck,
    Runtime.makeInstance, Runtime.getFloat64, Runtime.setFloat64, Runtime.setFloat64Values,
    Runtime.doStep, Runtime.initialTime, Runtime.eventTime, Runtime.completedTime,
    CInitialization.Emission.statement, CInitialization.value,
    Runtime.raiseField, Runtime.mode, Runtime.field, Runtime.x])

theorem body_calls (m : Solve.FMI3Model source) (sig : Signature) :
    ∀ stmt ∈ Runtime.body m sig, Lowering.CallsWellFormed stmt := by
  unfold Runtime.body
  split <;> fmi_literal_calls
  all_goals split <;> fmi_literal_calls

theorem functions_calls (m : Solve.FMI3Model source) (signatures : List Signature) :
    ∀ fn ∈ functions m signatures, ∀ stmt ∈ fn.body, Lowering.CallsWellFormed stmt := by
  intro fn member
  rcases List.mem_append.mp member with helper | exported
  · simp [Runtime.helpers] at helper
    rcases helper with rfl | rfl | rfl <;> fmi_literal_calls
  · obtain ⟨sig, member, rfl⟩ := List.mem_map.mp exported
    exact body_calls m sig

/-- Collection, binding and pass behavior for the actual rendered function
list. External-call and whole-file validity obligations are not assumed away:
the conclusion is equality of this authored machine's complete observations. -/
theorem lowering_behaviors (m : Solve.FMI3Model source) (signatures : List Signature)
    {pool : Pool (excluded ++ (functions m signatures).flatMap functionNames)}
    (made : prepare m signatures = some pool) (firstBlock : Nat)
    (name : String) (args : List Value) (heap : Heap)
    (behavior : Transition.Observation CBody.Result) :
    ((@CCalls.Typed.machine (pool.namedInterface cInterface firstBlock)
        (Lowering.program pool.symbols (program m signatures))).Behaves
      (.calling name args heap .done) behavior ↔
    (@CCalls.Typed.machine (pool.interface cInterface firstBlock) (program m signatures)).Behaves
      (.calling name args heap .done) behavior) :=
  (Pool.forFunctions_behaviors made cInterface firstBlock (header_fresh m signatures pool)
    (program m signatures) (program_covered m signatures) (functions_calls m signatures)
    name args heap behavior).2

end Rumoca.FMI3.LiteralPreparation
