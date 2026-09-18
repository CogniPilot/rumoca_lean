import RumocaC.CallPolicyExecution

/-! A decidable no-heap and acyclic call-graph policy over the complete
generated C call graph, together with the connection to eventful call
resolution. `NoHeap` classifies every callee name occurring in a function body
against a named boundary set (defined functions, declared kernel entries,
header-declared FMI functions and named non-allocating externals) and rejects
every allocation entry point. `Acyclic` states that the direct-call relation
among defined functions has no cycle, with a decidable rank (topological order)
sufficient condition. The semantic theorems show that a call actually scheduled
from a policy-checked body names a permitted, non-allocating target; a search
for `malloc` is not used as evidence anywhere. Indirect (function-pointer)
targets and native ABI/linking remain separate resolution boundaries. -/
noncomputable section
namespace Rumoca.CCallPolicy
open CTree CMemory CCalls

/-! ### The no-heap syntactic policy -/

/-- Allocation entry points a no-heap generated call graph must never name
directly. The set is listed explicitly; it is not derived from a text search. -/
def allocationNames : List String :=
  ["malloc", "calloc", "realloc", "reallocarray", "free", "aligned_alloc",
   "posix_memalign", "memalign", "valloc", "pvalloc", "strdup", "strndup"]

/-- Named non-allocating call targets a no-heap policy admits, grouped by role:
generated helper/definition names the graph targets by name, declared numerical
kernel entries, header-declared FMI functions, non-allocating C library / math /
atomic externals, and the importer-provided logger callback. -/
structure Externals where
  generated : List String
  kernel : List String
  header : List String
  library : List String
  callback : List String

/-- A name admitted by the external boundary set (in any of its roles). -/
def Externals.allows (b : Externals) (name : String) : Bool :=
  b.generated.contains name || b.kernel.contains name || b.header.contains name ||
    b.library.contains name || b.callback.contains name

/-- The names of the generated function definitions in a function list. -/
def definedNames (defs : List Function) : List String :=
  defs.map (fun fn => fn.signature.name)

/-- Every callee name occurring in one function body, including calls to helper
and kernel entries. An indirect (function-pointer) callee has no name and is
not listed here; it is a separate resolution boundary. -/
def CallGraph.calls (fn : Function) : List String :=
  (fn.body.flatMap statementCalls).filterMap fun
    | .id name => some name
    | _ => none

/-- One call expression admitted by the no-heap policy: a direct call to a
defined function or a named boundary target that is not an allocation entry
point. An indirect callee is left to the separate function-pointer boundary. -/
def NoHeapCallee (defs : List Function) (b : Externals) : Expr → Bool
  | .id name => ((definedNames defs).contains name || b.allows name) &&
      !allocationNames.contains name
  | _ => true

/-- The decidable no-heap policy over a complete generated call graph and a
named external boundary set: every callee in every function body is admitted. -/
def NoHeap (defs : List Function) (b : Externals) : Bool :=
  defs.all (checkFunction (NoHeapCallee defs b))

/-- Monotonicity of the body checker: relaxing the admitted-callee predicate
preserves a passing check. The two checkers walk the same call inventory. -/
theorem checkFunction_mono {c₁ c₂ : Expr → Bool} (imp : ∀ e, c₁ e = true → c₂ e = true)
    (fn : Function) (checked : checkFunction c₁ fn = true) : checkFunction c₂ fn = true := by
  rw [checkFunction_inventory] at checked ⊢
  exact List.all_eq_true.mpr fun e mem => imp e (List.all_eq_true.mp checked e mem)

/-- A direct callee admitted by the no-heap policy names no allocation entry
point, and is a defined function or a named boundary target. -/
theorem noHeap_callee_named {defs : List Function} {b : Externals} {name : String}
    (permitted : NoHeapCallee defs b (.id name) = true) :
    allocationNames.contains name = false ∧
      ((definedNames defs).contains name = true ∨ b.allows name = true) := by
  simp only [NoHeapCallee, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at permitted
  exact ⟨permitted.2, permitted.1⟩

/-! ### No allocation along scheduled call steps -/

/-- The initial body of a no-heap-checked function is policy-ready: every
pending statement admits only permitted, non-allocating callees. -/
theorem noHeap_body_ready {defs : List Function} {b : Externals} (fn : Function)
    (env : CBody.Locals) (types : CLoops.Types) (heap : Heap)
    (checked : checkFunction (NoHeapCallee defs b) fn = true) :
    LoopReady (fun e => NoHeapCallee defs b e = true) (.running fn.body env types heap) :=
  fun stmt member => (checkFunction_correct _ fn).mp checked stmt member

/-- A call actually scheduled by the shared eventful resolver from a
policy-ready body names no allocation entry point, and names a defined function
or a named boundary target. This is the no-heap guarantee stated over the
machine's own call step, not over a search for allocation identifiers. -/
theorem noHeap_no_alloc_call [CInterface] {E : Type} (program : Events.Program E)
    (foreign : ForeignAddresses program) {defs : List Function} {b : Externals}
    {state : CLoops.State} {resultType : String} {stack : Typed.Continuation}
    {name : String} {args : List Value} {after : Heap} {later : Typed.Continuation}
    {definition : Definition}
    (ready : LoopReady (fun e => NoHeapCallee defs b e = true) state)
    (stepped : Events.internalNext program (.body state resultType stack) =
      some (.calling name args after later))
    (target : program.internal.definitions name = some definition) :
    allocationNames.contains name = false ∧
      ((definedNames defs).contains name = true ∨ b.allows name = true) := by
  cases state with
  | returned result =>
      simp [Events.internalNext, Typed.nextWith, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at stepped
  | running code env types heap =>
      simp only [Events.internalNext, Typed.nextWith] at stepped
      cases next : CLoops.next (.running code env types heap) with
      | some following => simp [next] at stepped
      | none =>
          simp only [next] at stepped
          cases code with
          | nil =>
              simp only [Events.enterCall] at stepped
              split at stepped <;> simp at stepped
          | cons stmt rest =>
              simp only [Events.enterCall, Option.bind_eq_bind, Option.bind_eq_some_iff] at stepped
              obtain ⟨operand, extracted, resolvedName, resolved, values, converted, emitted⟩ := stepped
              have names := (Typed.State.calling.inj (Option.some.inj emitted)).1
              rw [names] at resolved
              have policy := ready stmt List.mem_cons_self
              have occurs := (statement_calls_complete _ _).mpr policy operand.callee
                (operand_callee stmt operand extracted)
              rw [named_origin env heap operand.callee
                (internal_resolution program foreign resolved target)] at occurs
              exact noHeap_callee_named occurs

/-- No allocation is ever scheduled along any execution that starts from a
no-heap-checked body: for every loop state the body reaches and every call the
shared eventful resolver then schedules to a defined target, the called name is
not an allocation entry point. -/
theorem noHeap_execution_no_alloc [CInterface] {E : Type} (program : Events.Program E)
    (foreign : ForeignAddresses program) {defs : List Function} {b : Externals} (fn : Function)
    (env : CBody.Locals) (types : CLoops.Types) (heap : Heap)
    {state : CLoops.State} {resultType : String} {stack : Typed.Continuation}
    {name : String} {args : List Value} {after : Heap} {later : Typed.Continuation}
    {definition : Definition}
    (checked : checkFunction (NoHeapCallee defs b) fn = true)
    (reached : Transition.Reaches CLoops.machine.step (.running fn.body env types heap) state)
    (stepped : Events.internalNext program (.body state resultType stack) =
      some (.calling name args after later))
    (target : program.internal.definitions name = some definition) :
    allocationNames.contains name = false :=
  (noHeap_no_alloc_call program foreign
    (loop_ready_reaches (noHeap_body_ready fn env types heap checked) reached) stepped target).1

/-! ### The acyclic call-graph policy -/

/-- The direct-call edge among defined functions: a call in `caller`'s body to a
name that is itself a defined function. Calls to declared kernel entries and to
named externals are leaves and contribute no edge. -/
def DefinedEdge (defs : List Function) (caller callee : String) : Prop :=
  ∃ fn ∈ defs, fn.signature.name = caller ∧
    .id callee ∈ fn.body.flatMap statementCalls ∧ callee ∈ definedNames defs

/-- The direct-call relation among defined functions has no cycle. -/
def Acyclic (defs : List Function) : Prop :=
  ∀ caller callee, DefinedEdge defs caller callee →
    ¬ Transition.Reaches (DefinedEdge defs) callee caller

private theorem reaches_measure {S : Type} {edge : S → S → Prop} {μ : S → Nat}
    (dec : ∀ {a b}, edge a b → μ b < μ a) {a b : S}
    (path : Transition.Reaches edge a b) : μ b ≤ μ a := by
  induction path with
  | refl => exact Nat.le_refl _
  | next first _ ih => exact Nat.le_trans ih (Nat.le_of_lt (dec first))

/-- Every defined-function edge strictly decreases a total rank on names,
provided every defined name carries a rank. This is the topological-order
witness of acyclicity. -/
theorem definedEdge_decreases {rank : String → Option Nat} {defs : List Function}
    {caller callee : String} (ranked : Ranked rank defs)
    (allRanked : ∀ fn ∈ defs, (rank fn.signature.name).isSome = true)
    (edge : DefinedEdge defs caller callee) :
    (rank callee).getD 0 < (rank caller).getD 0 := by
  obtain ⟨fn, member, rfl, calls, calleeDefined⟩ := edge
  obtain ⟨c, hc, lowers⟩ := ranked fn member
  simp only [definedNames, List.mem_map] at calleeDefined
  obtain ⟨fn', member', hname⟩ := calleeDefined
  have isSome := allRanked fn' member'
  rw [hname] at isSome
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp isSome
  have lt := lowers callee calls t ht
  rw [hc, ht]
  simpa using lt

/-- A decidable rank check that assigns a rank to every defined function and
lowers along every direct call implies the call graph is acyclic. The rank is a
topological order; `checkRanks` and the `isSome` check are both decidable. -/
theorem acyclic_of_ranked {rank : String → Option Nat} {defs : List Function}
    (ranked : Ranked rank defs)
    (allRanked : ∀ fn ∈ defs, (rank fn.signature.name).isSome = true) :
    Acyclic defs := by
  intro caller callee edge path
  have lower := definedEdge_decreases ranked allRanked edge
  have upper := reaches_measure (fun {_ _} e => definedEdge_decreases ranked allRanked e) path
  omega

end Rumoca.CCallPolicy
