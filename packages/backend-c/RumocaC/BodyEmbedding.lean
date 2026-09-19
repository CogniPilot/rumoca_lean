import RumocaC.TypedCallProofs
import RumocaC.CallParameters

/-! Embed successful memory-body execution in the typed loop/call machine.
The relation retains the code, values and heap and supplies local type bindings.
Nested declarations are excluded explicitly because neither machine provides
C block scopes. This is not a simulation of foreign calls or printed C. -/
namespace Rumoca.CBodyEmbedding
open CTree CMemory
variable [interface : CInterface]

omit interface in
private theorem add_comparison_none (a b : Value) : CBody.comparison .add a b = none := by
  cases a <;> cases b <;> simp [CBody.comparison, CBody.floatComparison, convert, Value.finite]

omit interface in
private theorem mul_comparison_none (a b : Value) : CBody.comparison .mul a b = none := by
  cases a <;> cases b <;> simp [CBody.comparison, CBody.floatComparison, convert, Value.finite]

omit interface in
private theorem sub_comparison_none (a b : Value) : CBody.comparison .sub a b = none := by
  cases a <;> cases b <;> simp [CBody.comparison, CBody.floatComparison, convert, Value.finite]

omit interface in
private theorem div_comparison_none (a b : Value) : CBody.comparison .div a b = none := by
  cases a <;> cases b <;> simp [CBody.comparison, CBody.floatComparison, convert, Value.finite]

theorem eval_refines (env : CBody.Locals) (types : CLoops.Types) (heap : Heap)
    (e : Expr) (value : Value) (h : CBody.eval env heap e = some value) :
    CLoops.eval env types heap e = some value := by
  cases e with
  | bin op a b =>
    cases op <;> try exact h
    all_goals
      simp only [CBody.eval] at h
      cases ha : CBody.eval env heap a <;> simp only [ha, bind, Option.bind_none, Option.bind_some] at h
      all_goals try contradiction
      all_goals cases hb : CBody.eval env heap b <;>
        simp_all only [Option.bind_none, Option.bind_some, add_comparison_none, mul_comparison_none,
          sub_comparison_none, div_comparison_none]
      all_goals contradiction
  | _ => exact h

/-- Nested declarations need a block-scope semantics. The existing memory-body
proofs embed when every nested block is declaration-free; top-level declarations
remain allowed and update the target's local type environment. -/
def closedBlocks : Stmt → Bool
  | .branch _ yes no => yes.all CLoops.noDeclarations && no.all CLoops.noDeclarations
  | .whileLoop _ body => body.all CLoops.noDeclarations
  | _ => true

def safe : CBody.State → Prop
  | .running code _ _ => code.all closedBlocks = true
  | .returned _ => True

def lift : CBody.State → CLoops.Types → CLoops.State
  | .running code env heap, types => .running code env types heap
  | .returned result, _ => .returned result

omit interface in
theorem noDeclarations_closed (stmt : Stmt) (h : CLoops.noDeclarations stmt = true) :
    closedBlocks stmt = true := by
  cases stmt <;> simp_all [closedBlocks, CLoops.noDeclarations]

omit interface in
theorem block_closed (code : List Stmt) (h : code.all CLoops.noDeclarations = true) :
    code.all closedBlocks = true := by
  apply List.all_eq_true.mpr
  intro stmt mem
  exact noDeclarations_closed stmt (List.all_eq_true.mp h stmt mem)

theorem next_refines (s t : CBody.State) (types : CLoops.Types)
    (hs : safe s) (h : CBody.next s = some t) :
    ∃ types', CLoops.next (lift s types) = some (lift t types') ∧ safe t := by
  cases s with
  | returned result => simp [CBody.next] at h
  | running code env heap =>
    cases code with
    | nil => simp [CBody.next] at h
    | cons stmt rest =>
      have ⟨hc, hr⟩ : closedBlocks stmt = true ∧ rest.all closedBlocks = true := by
        simpa [safe] using hs
      cases stmt with
      | declare type name expr =>
        cases hv : CBody.eval env heap expr with
        | none => simp [CBody.next, hv] at h
        | some value =>
          have ev := eval_refines env types heap expr value hv
          cases ht : interface.types type with
          | none => simp [CBody.next, CBody.cast, hv, ht] at h
          | some declared =>
            cases hd : convert declared value with
            | none => simp [CBody.next, CBody.cast, hv, ht, hd] at h
            | some converted =>
              cases hn : env name with
              | some previous => simp [CBody.next, CBody.cast, hv, ht, hn] at h
              | none =>
                simp [CBody.next, CBody.cast, hv, ht, hd, hn] at h
                subst t
                exact ⟨CLoops.bindType types name declared,
                  by simp [CLoops.next, lift, ev, ht, hd, hn], hr⟩
      | assign target expr =>
        cases hv : CBody.eval env heap expr with
        | none => simp [CBody.next, hv] at h
        | some value =>
          have ev := eval_refines env types heap expr value hv
          cases hp : CBody.lvalue env heap target with
          | none => simp [CBody.next, hv, hp] at h
          | some address =>
            cases hh : store heap address value with
            | none => simp [CBody.next, hv, hp, hh] at h
            | some heap' =>
              simp [CBody.next, hv, hp, hh] at h
              subst t
              refine ⟨types, ?_, hr⟩
              cases target <;> simp_all [lift, CLoops.next, CBody.lvalue]
      | eval expr =>
        cases hv : CBody.eval env heap expr with
        | none => simp [CBody.next, hv] at h
        | some value =>
          have ev := eval_refines env types heap expr value hv
          simp [CBody.next, hv] at h
          subst t
          exact ⟨types, by simp [CLoops.next, lift, ev], hr⟩
      | ret expr =>
        cases expr with
        | none =>
          simp [CBody.next] at h
          subst t
          exact ⟨types, rfl, trivial⟩
        | some expr =>
          cases hv : CBody.eval env heap expr with
          | none => simp [CBody.next, hv] at h
          | some value =>
            have ev := eval_refines env types heap expr value hv
            simp [CBody.next, hv] at h
            subst t
            exact ⟨types, by simp [CLoops.next, lift, ev], trivial⟩
      | branch condition yes no =>
        cases hv : CBody.eval env heap condition with
        | none => simp [CBody.next, hv] at h
        | some value =>
          have ev := eval_refines env types heap condition value hv
          cases ht : value.truth with
          | none => simp [CBody.next, hv, ht] at h
          | some takeYes =>
            simp [CBody.next, hv, ht] at h
            subst t
            refine ⟨types, ?_, ?_⟩
            · have hb : (yes.all CLoops.noDeclarations && no.all CLoops.noDeclarations) = true := hc
              simp [lift, CLoops.next, hb, ev, ht]
            · have ⟨hy, hn⟩ : yes.all CLoops.noDeclarations = true ∧ no.all CLoops.noDeclarations = true := by
                simpa only [closedBlocks, Bool.and_eq_true] using hc
              cases takeYes <;> simp [safe, hr, block_closed yes hy, block_closed no hn]
      | whileLoop condition body =>
        cases hv : CBody.eval env heap condition with
        | none => simp [CBody.next, hv] at h
        | some value =>
          have ev := eval_refines env types heap condition value hv
          cases ht : value.truth with
          | none => simp [CBody.next, hv, ht] at h
          | some again =>
            simp [CBody.next, hv, ht] at h
            subst t
            refine ⟨types, ?_, ?_⟩
            · have hb : body.all CLoops.noDeclarations = true := hc
              simp [lift, CLoops.next, hb, ev, ht]
            · cases again <;> simp [safe, hr, hc, block_closed body hc]

theorem run_refines (n : Nat) (s t : CBody.State) (types : CLoops.Types)
    (hs : safe s) (h : CBody.run n s = some t) :
    ∃ types', CLoops.run n (lift s types) = some (lift t types') ∧ safe t := by
  induction n generalizing s types with
  | zero =>
    have eq : s = t := Option.some.inj h
    subst t
    exact ⟨types, rfl, hs⟩
  | succ n ih =>
    cases hn : CBody.next s with
    | none => simp [CBody.run, hn] at h
    | some u =>
      obtain ⟨types', step, safeU⟩ := next_refines s u types hs hn
      have tail : CBody.run n u = some t := by simpa [CBody.run, hn] using h
      obtain ⟨types'', run, safeT⟩ := ih u types' safeU tail
      exact ⟨types'', by simpa [CLoops.run, step] using run, safeT⟩

noncomputable section
/-- Successful body execution enters the typed caller's ordinary return
continuation. The same body, locals and heap are retained. -/
theorem typed_return_reaches (program : CCalls.Program) (state : CBody.State)
    (types : CLoops.Types) (result : CBody.Result) (returnType : String)
    (returned : Value) (stack : CCalls.Typed.Continuation) (n : Nat)
    (hs : safe state) (h : CBody.run n state = some (.returned result))
    (cast : CCalls.returnCast returnType result.value = some returned) :
    Transition.Reaches (CCalls.Typed.machine program).step
      (.body (lift state types) returnType stack) (.returning returned result.heap stack) := by
  obtain ⟨types', execution, _⟩ := run_refines n state (.returned result) types hs h
  have reach := CCalls.Typed.body_reaches program (CLoops.run_reaches execution) returnType stack
  exact reach.trans (.next (by simp [CCalls.Typed.machine, CCalls.Typed.next, lift, cast, CCalls.Typed.nextWith]) (.refl _))

/-- Every behavior of the typed target equals the checked body's converted
result. In particular, the new machine cannot add a stuck or divergent outcome. -/
theorem typed_body_behaviors (program : CCalls.Program) (state : CBody.State)
    (types : CLoops.Types) (result : CBody.Result) (returnType : String)
    (returned : Value) (n : Nat)
    (hs : safe state) (h : CBody.run n state = some (.returned result))
    (cast : CCalls.returnCast returnType result.value = some returned) (behavior) :
    (CCalls.Typed.machine program).Behaves (.body (lift state types) returnType .done) behavior ↔
      behavior = .terminates ⟨returned, result.heap⟩ := by
  apply (CCalls.Typed.machine program).behavior_iff
  · exact (typed_return_reaches program state types result returnType returned .done n hs h cast).trans
      (.next (by rfl) (.refl _))
  · rfl

/-- Enter a function with checked argument conversions, execute its body and
return under any caller. The matching local types follow from successful
binding; callers do not get to supply an unrelated type environment. -/
theorem typed_call_reaches (program : CCalls.Program) (fn : CTree.Function)
    (args : List Value) (env : CBody.Locals) (heap : Heap)
    (result : CBody.Result) (returned : Value) (stack : CCalls.Typed.Continuation) (n : Nat)
    (defined : program.definitions fn.signature.name = some (.tree fn))
    (bound : CCalls.parameters fn.signature.parameters args = some env)
    (closed : fn.body.all closedBlocks = true)
    (executed : CBody.run n (.running fn.body env heap) = some (.returned result))
    (cast : CCalls.returnCast fn.signature.result result.value = some returned) :
    Transition.Reaches (CCalls.Typed.machine program).step
      (.calling fn.signature.name args heap stack) (.returning returned result.heap stack) := by
  obtain ⟨types, typed, _⟩ := CCalls.Parameters.parameters_typed _ _ _ bound
  exact .next (CCalls.Typed.tree_entry program fn.signature.name args heap stack fn env types
      defined bound typed)
    (typed_return_reaches program (.running fn.body env heap) types result fn.signature.result
      returned stack n closed executed cast)

/-- All complete-call behaviors, including failure and divergence, are
accounted for by the checked body run and ordinary entry/return conversion. -/
theorem typed_call_behaviors (program : CCalls.Program) (fn : CTree.Function)
    (args : List Value) (env : CBody.Locals) (heap : Heap)
    (result : CBody.Result) (returned : Value) (n : Nat)
    (defined : program.definitions fn.signature.name = some (.tree fn))
    (bound : CCalls.parameters fn.signature.parameters args = some env)
    (closed : fn.body.all closedBlocks = true)
    (executed : CBody.run n (.running fn.body env heap) = some (.returned result))
    (cast : CCalls.returnCast fn.signature.result result.value = some returned) (behavior) :
    (CCalls.Typed.machine program).Behaves (.calling fn.signature.name args heap .done) behavior ↔
      behavior = .terminates ⟨returned, result.heap⟩ := by
  apply (CCalls.Typed.machine program).behavior_iff
  · exact (typed_call_reaches program fn args env heap result returned .done n
      defined bound closed executed cast).trans (.next rfl (.refl _))
  · rfl
end

end Rumoca.CBodyEmbedding
