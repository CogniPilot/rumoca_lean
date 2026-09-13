import RumocaFMI3.FactoryArguments
import RumocaFMI3.FactoryRejection

/-! Public factory prefixes. ME enters validation immediately; CS first
rejects requested capabilities outside the declared unit profile. -/
noncomputable section
namespace Rumoca.FMI3.FactoryEntry
open CTree CMemory CBody FactoryArguments
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

def unsupported (args : Raw) : Bool := args.events || decide (args.intermediateCount.val ≠ 0)

theorem coSimulation_guard (program : CCalls.Events.Program E) (model : Solve.FMI3Model source)
    (args : Raw) (types : CLoops.Types) (heap : Heap) (stack : CCalls.Typed.Continuation) :
    CCalls.Events.internalNext program
      (.body (.running (Runtime.body model (signature .cs)) (parameters .cs args) types heap)
        "fmi3Instance" stack) =
      some (.body (.running
        ((if unsupported args then FactoryRejection.code "Events and intermediate updates are unsupported" else []) ++
          Runtime.makeInstance model .cs) (parameters .cs args) types heap) "fmi3Instance" stack) := by
  have condition : eval (parameters .cs args) heap
      (Runtime.either (Runtime.v "eventModeUsed")
        (Runtime.nev (Runtime.v "nRequiredIntermediateVariables") (Runtime.n 0))) =
      some (boolean (unsupported args)) := by
    cases flag : args.events <;>
      simp [parameters, CCalls.Signature.locals, signature, arguments, List.lookup, eval,
        resolve, Runtime.either, Runtime.v, Runtime.nev, Runtime.n, comparison,
        boolean, Value.truth, unsupported, flag]
  simp only [Runtime.body, signature, Identity.factoryName]
  simp only [Runtime.either, Runtime.nev] at condition ⊢
  simp [CCalls.Events.internalNext, CCalls.Typed.nextWith, CLoops.next, CLoops.eval,
    CLoops.noDeclarations, Runtime.branch, Runtime.ret, condition, FactoryRejection.code,
    FactoryRejection.logCall, boolean, Value.truth]

theorem validation_entry (program : CCalls.Events.Program E) (model : Solve.FMI3Model source)
    (kind : Kind) (args : Raw) (heap : Heap) (stack : CCalls.Typed.Continuation)
    (defined : program.internal.definitions (signature kind).name =
      some (.tree (Runtime.function model (signature kind))))
    (supported : kind = .me ∨ unsupported args = false) :
    ∃ types,
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.calling (signature kind).name (arguments kind args) heap stack)
        (.body (.running (Runtime.makeInstance model kind) (parameters kind args) types heap)
          "fmi3Instance" stack) ∧
      CCalls.Parameters.Coherent (parameters kind args) types ∧ Scope args (parameters kind args) := by
  obtain ⟨types, entered, coherent, scope⟩ := FactoryArguments.call_entry program model kind args heap stack defined
  refine ⟨types, ?_, coherent, scope⟩
  cases kind with
  | me => exact .next entered (.refl _)
  | cs =>
    have allowed : unsupported args = false := supported.resolve_left (by decide)
    have guarded := coSimulation_guard program model args types heap stack
    rw [allowed] at guarded
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append] at guarded
    exact .next entered (.next guarded (.refl _))

end Rumoca.FMI3.FactoryEntry
