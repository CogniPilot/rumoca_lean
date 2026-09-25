import RumocaCore.GALEC.Elaboration.Signals.Reachability
import RumocaCore.GALEC.Elaboration.Bodies.Lowering

/-! Soundness of the §1.5 analysis against execution with error signals: for
every lowered body, every arithmetic and finiteness interpretation and every
execution, a run that starts within the in-reachable set ends within the
computed out-reachable set. Loops use the stop equation of the widening, not a
least-fixed-point property. -/
namespace Rumoca.GALEC.Elaboration.Reach
open Rumoca.Tensor Rumoca.Solve.Tensor

theorem subset_refl (set : SignalSet) : SignalSet.Subset set set := fun _ present => present

theorem subset_trans {first second third : SignalSet} (left : SignalSet.Subset first second)
    (right : SignalSet.Subset second third) : SignalSet.Subset first third :=
  fun signal present => right signal (left signal present)

theorem subset_union_left (first second : SignalSet) : SignalSet.Subset first (first.union second) :=
  fun signal present => by simp [present]

theorem subset_union_right (first second : SignalSet) : SignalSet.Subset second (first.union second) :=
  fun signal present => by simp [present]

theorem union_subset {first second third : SignalSet} (left : SignalSet.Subset first third)
    (right : SignalSet.Subset second third) : SignalSet.Subset (first.union second) third := by
  intro signal present
  simp only [SignalSet.contains_union, Bool.or_eq_true] at present
  rcases present with found | found
  · exact left signal found
  · exact right signal found

theorem diff_subset {first second : SignalSet} (within : SignalSet.Subset first second)
    (tested : SignalSet) : SignalSet.Subset (first.diff tested) (second.diff tested) := by
  intro signal present
  simp only [SignalSet.contains_diff, Bool.and_eq_true, Bool.not_eq_true'] at present ⊢
  exact ⟨within signal present.1, present.2⟩

/-- A state that misses every tested signal stays within the set with the
tested signals removed. -/
theorem missed_subset {first second tested : SignalSet} (within : SignalSet.Subset first second)
    (missed : ¬ SignalSet.Meets tested first) : SignalSet.Subset first (second.diff tested) := by
  intro signal present
  simp only [SignalSet.contains_diff, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨within signal present, ?_⟩
  cases found : tested.contains signal
  · rfl
  · exact absurd ⟨signal, found, present⟩ missed

/-- An iteration whose every step keeps the signal set within `set` does so overall. -/
theorem iteration_within {step : Fin bound → σ × SignalSet → σ × SignalSet → Prop} {set : SignalSet}
    (kept : ∀ i current next, step i current next → SignalSet.Subset current.2 set →
      SignalSet.Subset next.2 set)
    (executed : Iteration.Executes step count first last)
    (start : SignalSet.Subset first.2 set) : SignalSet.Subset last.2 set := by
  induction executed with
  | zero state => exact start
  | next within _ body ih => exact kept _ _ _ body (ih start)

variable {inputs outputs : List Shape} {table : BindingTable inputs outputs}
  {HasShape : List String → Shape → Prop} {ceiling : Nat}

/-- A lowered condition's state change stays within its out-reachable set on
both outcomes of the condition. -/
theorem condition_sound {bounds : List Nat} {names : IteratorNames bounds} {test : AST.Condition}
    {cond : Condition inputs outputs bounds}
    (typed : ConditionLowering.Elaborates table names test cond)
    (analyzed : condition true incoming test = some tested)
    (step : BinaryOp → α → α → α → Prop) (finite : α → Prop) (zero one : α)
    (input : Env α inputs) (env : IteratorEnv bounds) (before : Signaled α outputs)
    (within : SignalSet.Subset before.2 incoming) :
    (cond.Holds step finite zero one @input before @env →
      SignalSet.Subset (cond.enter before).2 tested) ∧
    (¬ cond.Holds step finite zero one @input before @env → SignalSet.Subset before.2 tested) := by
  cases typed with
  | finite argument =>
    cases Option.some.inj analyzed
    exact ⟨fun _ => within, fun _ => within⟩
  | signalIn denoted =>
    simp only [condition, Option.bind_eq_some_iff] at analyzed
    obtain ⟨set, read, admitted⟩ := analyzed
    cases SignalNames.denotes_unique ((SignalNames.read_iff _ _).mp read) denoted
    split at admitted
    · cases Option.some.inj admitted
      exact ⟨fun _ => diff_subset within _, fun missed => missed_subset within missed⟩
    · contradiction

mutual
theorem statement_sound {bounds : List Nat} {names : IteratorNames bounds}
    {source : AST.Statement} {stmt : Statement inputs outputs bounds}
    (typed : Bodies.StatementElaborates table HasShape ceiling names source stmt)
    (analyzed : statement true incoming source = some out)
    (step : BinaryOp → α → α → α → Prop) (finite : α → Prop) (zero one : α)
    (input : Env α inputs) (env : IteratorEnv bounds) (before after : Signaled α outputs)
    (ran : stmt.Runs step finite zero one @input @env before after)
    (within : SignalSet.Subset before.2 incoming) : SignalSet.Subset after.2 out := by
  match source, typed with
  | _, .assign assignment =>
    cases assignment with
    | assign target value =>
      rw [statement] at analyzed
      cases Option.some.inj analyzed
      rw [ran.2]
      exact within
  | .ifThen (first :: rest) otherwise, .branch chosen =>
    rw [statement] at analyzed
    obtain ⟨⟨last, bodies⟩, conditioned, remaining⟩ := Option.bind_eq_some_iff.mp analyzed
    obtain ⟨others, alternated, same⟩ := Option.map_eq_some_iff.mp remaining
    cases same
    exact branches_sound chosen conditioned alternated step finite zero one @input @env before after
      ran within
  | .forLoop binder start stride stop body, .loop header typedBody =>
    rw [statement] at analyzed
    obtain ⟨fixed, _, remaining⟩ := Option.bind_eq_some_iff.mp analyzed
    obtain ⟨reached, checkedBody, stopped⟩ := Option.bind_eq_some_iff.mp remaining
    split at stopped
    · rename_i stop
      have fixedOut := Option.some.inj stopped
      rw [fixedOut] at stop checkedBody
      exact iteration_within (fun i current next bodyRan inside =>
          subset_trans (statements_sound typedBody checkedBody step finite zero one @input _
            current next bodyRan inside) (stop ▸ subset_union_right incoming reached)) ran
        (subset_trans within (stop ▸ subset_union_left incoming reached))
    · contradiction
  | .signal (first :: rest), .signal denoted =>
    rw [statement] at analyzed
    obtain ⟨set, read, same⟩ := Option.map_eq_some_iff.mp analyzed
    cases same
    cases SignalNames.denotes_unique ((SignalNames.read_iff _ _).mp read) denoted
    simp only [Statement.Runs] at ran
    subst ran
    intro signal present
    simp only [SignalSet.contains_union, Bool.or_eq_true] at present ⊢
    rcases present with found | found
    · exact Or.inl (within signal found)
    · exact Or.inr found
termination_by sizeOf source

theorem branches_sound {bounds : List Nat} {names : IteratorNames bounds}
    {sources : List (AST.Condition × List AST.Statement)} {otherwise : Option (List AST.Statement)}
    {stmt : Statement inputs outputs bounds}
    (typed : Bodies.BranchesElaborates table HasShape ceiling names sources otherwise stmt)
    (conditioned : conditional true incoming sources = some (last, bodies))
    (alternated : alternative true last otherwise = some others)
    (step : BinaryOp → α → α → α → Prop) (finite : α → Prop) (zero one : α)
    (input : Env α inputs) (env : IteratorEnv bounds) (before after : Signaled α outputs)
    (ran : stmt.Runs step finite zero one @input @env before after)
    (within : SignalSet.Subset before.2 incoming) :
    SignalSet.Subset after.2 (last.union (bodies.union others)) := by
  match sources, otherwise, typed with
  | [], none, .none =>
    rw [conditional] at conditioned
    cases Option.some.inj conditioned
    change after = before at ran
    subst ran
    exact subset_trans within (subset_union_left _ _)
  | [], some body, .otherwise typedBody =>
    rw [conditional] at conditioned
    cases Option.some.inj conditioned
    rw [alternative] at alternated
    exact subset_trans (statements_sound typedBody alternated step finite zero one @input @env
      before after ran within)
      (subset_trans (subset_union_right _ others) (subset_union_right _ _))
  | (test, body) :: rest, otherwise, .cons tested typedBody typedRest =>
    rw [conditional] at conditioned
    obtain ⟨⟨afterTest, reached⟩, branched, remaining⟩ := Option.bind_eq_some_iff.mp conditioned
    obtain ⟨⟨last', bodies'⟩, restConditioned, same⟩ := Option.map_eq_some_iff.mp remaining
    cases same
    rw [branch] at branched
    obtain ⟨afterTest', condAnalyzed, remaining⟩ := Option.bind_eq_some_iff.mp branched
    obtain ⟨reached', bodyAnalyzed, same⟩ := Option.map_eq_some_iff.mp remaining
    cases same
    obtain ⟨entered, missed⟩ := condition_sound tested condAnalyzed step finite zero one @input @env
      before within
    rcases ran with ⟨holds, yes⟩ | ⟨fails, no⟩
    · have result := statements_sound typedBody bodyAnalyzed step finite zero one @input @env
        _ after yes (entered holds)
      exact subset_trans result (subset_trans (subset_union_left reached bodies')
        (subset_trans (subset_union_left _ others) (subset_union_right last _)))
    · have result := branches_sound typedRest restConditioned alternated step finite zero one
        @input @env before after no (missed fails)
      intro signal present
      have found := result signal present
      simp only [SignalSet.contains_union, Bool.or_eq_true] at found ⊢
      tauto
termination_by sizeOf sources + sizeOf otherwise

theorem statements_sound {bounds : List Nat} {names : IteratorNames bounds}
    {sources : List AST.Statement} {stmt : Statement inputs outputs bounds}
    (typed : Bodies.BodyElaborates table HasShape ceiling names sources stmt)
    (analyzed : statements true incoming sources = some out)
    (step : BinaryOp → α → α → α → Prop) (finite : α → Prop) (zero one : α)
    (input : Env α inputs) (env : IteratorEnv bounds) (before after : Signaled α outputs)
    (ran : stmt.Runs step finite zero one @input @env before after)
    (within : SignalSet.Subset before.2 incoming) : SignalSet.Subset after.2 out := by
  match sources, typed with
  | [], .nil =>
    rw [statements] at analyzed
    cases Option.some.inj analyzed
    change after = before at ran
    subst ran
    exact within
  | source :: rest, .cons firstTyped restTyped =>
    rw [statements] at analyzed
    obtain ⟨reached, firstAnalyzed, restAnalyzed⟩ := Option.bind_eq_some_iff.mp analyzed
    obtain ⟨middle, firstRan, restRan⟩ := ran
    exact statements_sound restTyped restAnalyzed step finite zero one @input @env middle after
      restRan (statement_sound firstTyped firstAnalyzed step finite zero one @input @env
        before middle firstRan within)
termination_by sizeOf sources
end

/-- A method body that starts with no signal set ends within its exposed set. -/
theorem exposes_sound {names : IteratorNames []} {method : AST.Method}
    {stmt : Statement inputs outputs []} {exposed : SignalSet}
    (typed : Bodies.BodyElaborates table HasShape ceiling names method.body stmt)
    (exposes : Exposes method exposed)
    (step : BinaryOp → α → α → α → Prop) (finite : α → Prop) (zero one : α)
    (input : Env α inputs) (env : IteratorEnv []) (before : Env α outputs)
    (after : Signaled α outputs)
    (ran : stmt.Runs step finite zero one @input @env ⟨@before, SignalSet.empty⟩ after) :
    SignalSet.Subset after.2 exposed :=
  statements_sound typed exposes.2 step finite zero one @input @env _ after ran
    (fun signal present => by simp at present)

/-- A loop body may test a signal that it sets later: the check sees the back
edge. This body is admitted and exposes exactly `OVERFLOW`. -/
def laterCheckMethod : AST.Method :=
  ⟨.ident "DoStep", [.ident Signal.overflow.name],
    [.forLoop (.ident "k") (.literal (.number "1")) none (.literal (.number "2"))
      [.ifThen [(.signalCheck none false [.ident Signal.overflow.name] none,
          [.signal [.ident Signal.overflow.name]])] none,
        .signal [.ident Signal.overflow.name]]],
    .ident "DoStep"⟩

theorem later_check_accepted : exposed laterCheckMethod = some (SignalSet.ofList [.overflow]) := by
  decide +kernel

end Rumoca.GALEC.Elaboration.Reach
