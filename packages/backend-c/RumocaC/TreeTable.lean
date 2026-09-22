import RumocaC.TypedCallProofs

/-! Ordered assembly of ordinary C function trees into the two existing call
tables. Lookup uses the supplied list verbatim: no sorting, added helpers or
kernel fallback. Name uniqueness is needed only to bind arbitrary members and
to extend an appended table without collisions.

The `Program` API requires a kernel field even for this tree-only table. Its
value is an arbitrary parameter; the lookup facts below are not a theorem of
execution reachability, event resolution or correspondence with emitted bytes.
-/
namespace Rumoca.CCalls.TreeTable
open CTree
set_option autoImplicit false

/-- First matching function in the supplied order. -/
def treeDefinitions (functions : List Function) : CLoops.Calls.Definitions :=
  fun name => functions.find? (fun fn => fn.signature.name == name)

/-- Every present definition is a tree from the supplied function list. -/
def treeProgram (functions : List Function) (unusedKernel : CSyntax.Program) : Program where
  definitions := fun name => (treeDefinitions functions name).map Definition.tree
  kernel := unusedKernel

/-- A successful lookup cannot invent a function or bind it under another name. -/
theorem lookup_some (functions : List Function) (name : String) (fn : Function)
    (found : treeDefinitions functions name = some fn) :
    fn ∈ functions ∧ fn.signature.name = name := by
  induction functions with
  | nil => simp [treeDefinitions] at found
  | cons head rest ih =>
      by_cases same : head.signature.name = name
      · have equal : head = fn := by simpa [treeDefinitions, same] using found
        subst fn
        exact ⟨by simp, same⟩
      · have tailFound : treeDefinitions rest name = some fn := by
          simpa [treeDefinitions, same] using found
        obtain ⟨member, named⟩ := ih tailFound
        exact ⟨List.mem_cons_of_mem head member, named⟩

/-- Unique names make every list member the selected definition at its name. -/
theorem lookup_member (functions : List Function) (fn : Function)
    (unique : (functions.map (fun f => f.signature.name)).Nodup)
    (member : fn ∈ functions) :
    treeDefinitions functions fn.signature.name = some fn := by
  unfold treeDefinitions
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

theorem program_lookup_iff (functions : List Function) (unusedKernel : CSyntax.Program)
    (name : String) (fn : Function) :
    (treeProgram functions unusedKernel).definitions name = some (.tree fn) ↔
      treeDefinitions functions name = some fn := by
  cases found : treeDefinitions functions name <;> simp [treeProgram, found]

theorem program_lookup_member (functions : List Function) (unusedKernel : CSyntax.Program)
    (fn : Function)
    (unique : (functions.map (fun f => f.signature.name)).Nodup)
    (member : fn ∈ functions) :
    (treeProgram functions unusedKernel).definitions fn.signature.name = some (.tree fn) := by
  exact (program_lookup_iff functions unusedKernel fn.signature.name fn).2
    (lookup_member functions fn unique member)

/-- A collision-free prefix preserves every definition of the appended table.
The combined-name premise includes both internal and cross-list collisions. -/
theorem extends_append (before functions : List Function) (unusedKernel : CSyntax.Program)
    (unique : ((before ++ functions).map (fun fn => fn.signature.name)).Nodup) :
    Typed.Extends (treeDefinitions functions)
      (treeProgram (before ++ functions) unusedKernel) := by
  intro name fn found
  obtain ⟨member, named⟩ := lookup_some functions name fn found
  have bound := program_lookup_member (before ++ functions) unusedKernel fn unique
    (List.mem_append_right before member)
  simpa only [named] using bound

/-- No lookup selects a kernel tag; this does not assert execution reachability. -/
theorem no_kernel (functions : List Function) (unusedKernel : CSyntax.Program)
    (name : String) (fn : CStatements.Function) :
    (treeProgram functions unusedKernel).definitions name ≠ some (.kernel fn) := by
  cases found : treeDefinitions functions name <;> simp [treeProgram, found]

end Rumoca.CCalls.TreeTable
