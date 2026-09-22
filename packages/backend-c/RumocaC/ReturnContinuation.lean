import RumocaC.Calls
import RumocaCore.Transition.Prefix
import RumocaCore.Transition.Simulation

/-! Return-call continuations never execute the statement suffix saved in
their caller frame. This observational law is independent of the function
table, permits recursion and retains wrong/divergent behavior. -/
noncomputable section
namespace Rumoca.CCalls.ReturnContinuation
open CTree CMemory CBody
variable [CInterface]

def restFor : Destination → List Stmt → List Stmt
  | .ret, _ => []
  | _, rest => rest

def trim : Continuation → Continuation
  | .done => .done
  | .caller destination rest env resultType outer =>
      .caller destination (restFor destination rest) env resultType (trim outer)

def normalize : State → State
  | .body state resultType stack => .body state resultType (trim stack)
  | .calling name args heap stack => .calling name args heap (trim stack)
  | .kernel state heap stack => .kernel state heap (trim stack)
  | .returning value heap stack => .returning value heap (trim stack)
  | .halted result => .halted result

omit [CInterface] in
theorem restFor_idempotent (destination : Destination) (rest : List Stmt) :
    restFor destination (restFor destination rest) = restFor destination rest := by
  cases destination <;> rfl

omit [CInterface] in
theorem trim_idempotent (stack : Continuation) : trim (trim stack) = trim stack := by
  induction stack with
  | done => rfl
  | caller destination rest env resultType outer ih =>
      simp only [trim, restFor_idempotent, ih]

omit [CInterface] in
theorem normalize_idempotent (state : State) : normalize (normalize state) = normalize state := by
  cases state <;> simp only [normalize, trim_idempotent]

theorem resume_commutes (value : Value) (heap : Heap) (stack : Continuation) :
    (resume value heap (trim stack)).map normalize = (resume value heap stack).map normalize := by
  cases stack with
  | done => rfl
  | caller destination rest env resultType outer =>
      cases destination <;> simp only [trim, restFor, resume, resumeWith, normalize, trim_idempotent,
        Bind.bind, Pure.pure, Option.map_bind, Function.comp_def, Option.map_some]
      split <;> simp only [Option.map_none, Option.map_bind, Function.comp_def, Option.map_some,
        normalize, trim_idempotent]

theorem enter_commutes (state : CBody.State) (resultType : String) (stack : Continuation) :
    (enterCall state resultType (trim stack)).map normalize =
      (enterCall state resultType stack).map normalize := by
  cases state with
  | returned result => rfl
  | running statements env heap =>
      cases statements with
      | nil =>
          simp only [enterCall, enterCallWith]
          split <;> simp only [Option.map_some, Option.map_none, normalize, trim_idempotent]
      | cons statement rest =>
          simp only [enterCall, enterCallWith]
          cases found : callOperand statement with
          | none => rfl
          | some item =>
              rcases item with ⟨destination, name, args⟩
              simp only [Bind.bind, Pure.pure, Option.bind_some]
              split
              · rfl
              · simp only [Option.map_bind, Function.comp_def]
                congr 1
                funext values
                simp only [Option.map_some, normalize, trim, trim_idempotent]

theorem next_commutes (program : Program) (state : State) :
    (next program (normalize state)).map normalize =
      (next program state).map normalize := by
  cases state with
  | halted result => rfl
  | returning value heap stack => exact resume_commutes value heap stack
  | calling name args heap stack =>
      simp only [normalize, next, nextWith, Bind.bind, Pure.pure, Option.map_bind, Function.comp_def]
      congr 1
      funext definition
      cases definition <;>
        simp only [Option.map_bind, Function.comp_def, Option.map_some, normalize, trim_idempotent]
  | kernel state heap stack =>
      cases state <;> simp only [normalize, next, nextWith, Bind.bind, Pure.pure, Option.map_bind, Function.comp_def, Option.map_some,
        trim_idempotent]
  | body state resultType stack =>
      cases state with
      | returned result =>
          simp only [normalize, next, nextWith, Bind.bind, Pure.pure, Option.map_bind, Function.comp_def, Option.map_some, trim_idempotent]
      | running statements env heap =>
          simp only [normalize, next, nextWith]
          cases stepped : CBody.nextWith CBody.legacyExpressions (.running statements env heap) with
          | none => exact enter_commutes _ resultType stack
          | some later => simp only [Option.map_some, normalize, trim_idempotent]

private def normalizedMachine (program : Program) : Transition.Machine State CBody.Result where
  step s t := (next program s).map normalize = some t
  final := (machine program).final
  deterministic first second := Option.some.inj (first.symm.trans second)
  final_stuck := by
    intro state result final later
    cases state <;> simp_all [machine, machineWith, next, nextWith]

private def simulation (program : Program) :
    Transition.FunctionalBisimulation (machine program) (normalizedMachine program) where
  map := normalize
  Valid := fun _ => True
  step := by
    intro state later _ stepped
    refine ⟨True.intro, ?_⟩
    change (next program (normalize state)).map normalize = some (normalize later)
    rw [next_commutes]
    change next program state = some later at stepped
    rw [stepped]
    rfl
  reflect := by
    intro state later _ stepped
    change (next program (normalize state)).map normalize = some later at stepped
    rw [next_commutes] at stepped
    cases original : next program state with
    | none => simp [original] at stepped
    | some nextState =>
        exact ⟨nextState, original, (Option.some.inj (by simpa only [original, Option.map_some] using stepped)).symm⟩
  final := by
    intro state _
    cases state <;> rfl

/-- Equality after deleting ignored return suffixes gives equivalence in
the original authored C machine, for all its observations. -/
theorem behaviors (program : Program) (same : normalize first = normalize second)
    (observed) :
    (machine program).Behaves first observed ↔ (machine program).Behaves second observed := by
  rw [← (simulation program).behaviors True.intro observed,
    ← (simulation program).behaviors True.intro observed]
  change (normalizedMachine program).Behaves (normalize first) observed ↔
    (normalizedMachine program).Behaves (normalize second) observed
  rw [same]

theorem returned_call_suffix (program : Program) (name : String) (args : List Value)
    (heap : Heap) (first second : List Stmt) (env : Locals) (resultType : String)
    (stack : Continuation) (observed) :
    (machine program).Behaves
      (.calling name args heap (.caller .ret first env resultType stack)) observed ↔
    (machine program).Behaves
      (.calling name args heap (.caller .ret second env resultType stack)) observed :=
  by apply behaviors program; rfl

theorem next_behaviors (program : Program) (state : State)
    (nonfinal : (machine program).final state = none) (observed) :
    (machine program).Behaves state observed ↔
      match next program state with
      | none => observed = .wrong
      | some later => (machine program).Behaves later observed := by
  cases stepped : next program state with
  | some later => exact Transition.Machine.step_behaviors (machine program) stepped
  | none =>
      have stuck : ∀ later, ¬ (machine program).step state later := by
        intro later nextStep
        change next program state = some later at nextStep
        simp [stepped] at nextStep
      constructor
      · intro execution
        cases execution with
        | terminates path final =>
            cases path with
            | refl => simp [nonfinal] at final
            | next first _ => exact (stuck _ first).elim
        | wrong => rfl
        | diverges trace initial steps => exact (stuck _ (initial ▸ steps 0)).elim
      · rintro rfl
        exact .wrong (.refl _) nonfinal stuck

theorem next_equal_behaviors (program : Program) (first second : State)
    (firstNonfinal : (machine program).final first = none)
    (secondNonfinal : (machine program).final second = none)
    (same : (next program first).map normalize = (next program second).map normalize)
    (observed) :
    (machine program).Behaves first observed ↔ (machine program).Behaves second observed := by
  rw [next_behaviors program first firstNonfinal, next_behaviors program second secondNonfinal]
  cases firstStep : next program first <;> cases secondStep : next program second <;>
    simp only [firstStep, secondStep, Option.map_some, Option.map_none] at same
  · rfl
  · cases same
  · cases same
  · exact behaviors program (Option.some.inj same) observed

theorem enter_return_suffix (operand : Option Expr) (first second : List Stmt)
    (env : Locals) (heap : Heap) (resultType : String) (stack : Continuation) :
    (enterCall (.running (.ret operand :: first) env heap) resultType stack).map normalize =
      (enterCall (.running (.ret operand :: second) env heap) resultType stack).map normalize := by
  cases operand with
  | none => rfl
  | some expr =>
      cases expr <;> try rfl
      rename_i fn args
      cases fn <;> try rfl
      simp only [enterCall, enterCallWith, callOperand, Bind.bind, Pure.pure, Option.bind_some]
      split
      · rfl
      · simp only [Option.map_bind, Function.comp_def, Option.map_some, normalize, trim, restFor]

/-- Even when the returned operand calls an arbitrary recursive function,
the suffix following return cannot affect termination, wrongness or divergence. -/
theorem return_body_suffix (program : Program) (operand : Option Expr)
    (first second : List Stmt) (env : Locals) (heap : Heap) (resultType : String)
    (stack : Continuation) (observed) :
    (machine program).Behaves (.body (.running (.ret operand :: first) env heap) resultType stack) observed ↔
    (machine program).Behaves (.body (.running (.ret operand :: second) env heap) resultType stack) observed := by
  apply next_equal_behaviors program _ _ rfl rfl
  have equal : CBody.next (.running (.ret operand :: first) env heap) =
      CBody.next (.running (.ret operand :: second) env heap) := by cases operand <;> rfl
  simp only [CBody.next] at equal
  simp only [next, nextWith, equal]
  cases stepped : CBody.nextWith CBody.legacyExpressions (.running (.ret operand :: second) env heap) with
  | some later => rfl
  | none => exact enter_return_suffix operand first second env heap resultType stack

end Rumoca.CCalls.ReturnContinuation
end
