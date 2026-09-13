import RumocaFMI3.IdentityCalls

/-! Complete rejection of null identity arguments without accessing any
caller string memory or invoking the string library. -/
noncomputable section
namespace Rumoca.FMI3.Identity
open CTree CMemory
variable [interface : CInterface]

theorem guards_reaches (program : CCalls.Events.Program E) (entries : List (String × Option Address))
    (env : CBody.Locals) (types : CLoops.Types) (heap : Heap) (rest : List Stmt) (stack : CCalls.Typed.Continuation)
    (boolean : interface.types "fmi3Boolean" = some .boolean) (voidPointer : interface.types "void *" = some .pointer)
    (present : ∀ entry ∈ entries, env entry.1 = some (.pointer entry.2)) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (entries.map (fun entry => nullCheck entry.1) ++ rest) env types heap) "fmi3Boolean" stack)
      (if entries.any (fun entry => entry.2.isNone) then .returning (CBody.boolean false) heap stack
       else .body (.running rest env types heap) "fmi3Boolean" stack) := by
  induction entries with
  | nil => exact .refl _
  | cons entry entries ih =>
    obtain ⟨field, pointer⟩ := entry
    have first := CCalls.Events.body_step program
      (null_step env types heap field pointer (entries.map (fun entry => nullCheck entry.1) ++ rest)
        (present (field, pointer) (by simp)) voidPointer) "fmi3Boolean" stack
    cases pointer with
    | none =>
      simp only [List.map_cons, List.cons_append, List.any_cons, Option.isNone_none,
        Bool.true_or, if_true] at first ⊢
      exact .next first (false_return program env types heap
        (entries.map (fun entry => nullCheck entry.1) ++ rest) stack boolean)
    | some address =>
      simp only [Option.isNone_some, Bool.false_eq_true, if_false, List.nil_append] at first
      simp only [List.map_cons, List.cons_append, List.any_cons, Option.isNone_some, Bool.false_or]
      exact .next first (ih (fun entry member => present entry (by simp [member])))

def nullArguments (args : Arguments) : Bool :=
  args.name.isNone || args.token.isNone || args.expected.isNone || args.whitespace.isNone

theorem checks_reject (program : CCalls.Events.Program E) (args : Arguments) (heap : Heap)
    (stack : CCalls.Typed.Continuation) (boolean : interface.types "fmi3Boolean" = some .boolean)
    (voidPointer : interface.types "void *" = some .pointer) (missing : nullArguments args = true) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (checks ++ body) (locals args 0 0 0) types heap) "fmi3Boolean" stack)
      (.returning (CBody.boolean false) heap stack) := by
  have run := guards_reaches program
    [("name", args.name), ("token", args.token), ("expected", args.expected), ("whitespace", args.whitespace)]
    (locals args 0 0 0) types heap body stack boolean voidPointer (by
      intro entry member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> simp [locals, parameterLocals, CBody.bind])
  have missing' : (args.name.isNone || (args.token.isNone || (args.expected.isNone || args.whitespace.isNone))) = true := by
    simpa only [nullArguments, Bool.or_assoc] using missing
  simpa only [checks, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, missing', if_true] using run

/-- Any missing pointer rejects before the first library call, for arbitrary
remaining pointer values and heap contents. -/
theorem null_call_equivalence (program : CCalls.Events.Program E) (args : Arguments)
    (pointer : interface.types "const char *" = some .pointer)
    (size : interface.types "size_t" = some .size) (integer : interface.types "int" = some .int32)
    (boolean : interface.types "fmi3Boolean" = some .boolean) (voidPointer : interface.types "void *" = some .pointer)
    (defined : program.internal.definitions function.signature.name = some (.tree function))
    (heap : Heap) (stack : CCalls.Typed.Continuation) (missing : nullArguments args = true) (behavior) :
    (CCalls.Events.machine program).Behaves (.calling function.signature.name args.values heap stack) behavior ↔
      (CCalls.Events.machine program).Behaves (.returning (CBody.boolean false) heap stack) behavior := by
  apply CCalls.Events.internal_prefix_behaviors program
  refine .next (CCalls.Events.tree_entry program _ args.values heap stack function _ _ defined
    (parameters_bound args pointer) (parameter_types pointer)) ?_
  exact (CCalls.Events.body_reaches program (CLoops.run_reaches (initialization args heap size integer))
    "fmi3Boolean" stack).trans (checks_reject program args heap stack boolean voidPointer missing)

theorem null_call_correct (program : CCalls.Events.Program E) (bindings : Bindings program)
    (defined : program.internal.definitions function.signature.name = some (.tree function))
    (args : Arguments) (heap : Heap) (missing : nullArguments args = true) (behavior) :
    (CCalls.Events.machine program).Behaves (.calling function.signature.name args.values heap .done) behavior ↔
      behavior = .terminates [] ⟨CBody.boolean false, heap⟩ := by
  rw [null_call_equivalence program args bindings.pointer bindings.size bindings.integer bindings.boolean
    bindings.voidPointer defined heap .done missing]
  exact (CCalls.Events.return_forced program _ heap).behaviors behavior

end Rumoca.FMI3.Identity
