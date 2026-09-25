import RumocaCore.GALEC.Elaboration.Signals.Names

/-! eFMI §3.2.5 §1.5 static signal propagation, computed once over the original
AST: the out-reachable signal set of each statement from its in-reachable set.
It also enforces the §1.4 test-set rule and admits error-signal checks only in
the form `signal in S1, ..., Sn`. Restricted interpretations of the candidate
draft: an empty branch or loop body contributes its in-reachable set; the
`else` body starts from the out-reachable set of the last branch condition;
the in-reachable set of a loop body's first statement includes the back edge;
it is computed by widening from the loop's in-reachable set until the back edge
adds nothing, and a body that does not stabilize within the six predefined
signals is rejected. The admitted Boolean
condition `isFinite` and every admitted expression have an empty signal-set. -/
namespace Rumoca.GALEC.Elaboration.Reach

/-- The out-reachable set of a branch condition, or `none` when the check form
is not admitted or violates the §1.4 test-set rule. -/
def condition (incoming : SignalSet) : AST.Condition → Option SignalSet
  | .expr _ => some incoming
  | .signalCheck none false tested none =>
      (SignalNames.read tested).bind fun set =>
        if set != SignalSet.empty && set.subset incoming then some (incoming.diff set) else none
  | .signalCheck .. => none

/-- Widen a loop's in-reachable set by the body's out-reachable set until the
back edge adds nothing; `none` when the body is rejected or does not
stabilize within the fuel. -/
def widen (incoming : SignalSet) (analyze : SignalSet → Option SignalSet) :
    Nat → SignalSet → Option SignalSet
  | fuel, current =>
      (analyze current).bind fun reached =>
        if incoming.union reached = current then some current
        else
          match fuel with
          | 0 => none
          | fuel + 1 => widen incoming analyze fuel (incoming.union reached)

mutual
def statement (incoming : SignalSet) : AST.Statement → Option SignalSet
  | .assign _ _ => some incoming
  | .ifThen branches otherwise =>
      (conditional incoming branches).bind fun (last, bodies) =>
        (alternative last otherwise).map fun rest => last.union (bodies.union rest)
  | .forLoop _ _ _ _ body =>
      widen incoming (fun current => statements current body) Signal.all.length incoming
  | .signal raised => (SignalNames.read raised).map incoming.union
termination_by structural source => source

/-- The out-reachable set of the last branch condition and the union of the
out-reachable sets of the branch bodies. -/
def conditional (incoming : SignalSet) :
    List (AST.Condition × List AST.Statement) → Option (SignalSet × SignalSet)
  | [] => some (incoming, SignalSet.empty)
  | first :: rest =>
      (branch incoming first).bind fun (tested, reached) =>
        (conditional tested rest).map fun (last, bodies) => (last, reached.union bodies)
termination_by structural branches => branches

/-- A branch body starts from the out-reachable set of its condition. -/
def branch (incoming : SignalSet) : AST.Condition × List AST.Statement → Option (SignalSet × SignalSet)
  | (test, body) =>
      (condition incoming test).bind fun tested =>
        (statements tested body).map fun reached => (tested, reached)
termination_by structural chosen => chosen

/-- The `else` body starts from the out-reachable set of the last condition. -/
def alternative (incoming : SignalSet) : Option (List AST.Statement) → Option SignalSet
  | none => some SignalSet.empty
  | some body => statements incoming body
termination_by structural otherwise => otherwise

def statements (incoming : SignalSet) : List AST.Statement → Option SignalSet
  | [] => some incoming
  | source :: rest => (statement incoming source).bind fun reached => statements reached rest
termination_by structural sources => sources
end

/-- §1.3: the interface names predefined signals and equals the out-reachable
set of an imaginary final statement; the body starts with no signal set. -/
def exposed (method : AST.Method) : Option SignalSet :=
  (SignalNames.read method.signals).bind fun declared =>
    (statements SignalSet.empty method.body).bind fun reached =>
      if reached = declared then some declared else none

def Exposes (method : AST.Method) (set : SignalSet) : Prop :=
  SignalNames.Denotes method.signals set ∧ statements SignalSet.empty method.body = some set

theorem exposed_iff (method : AST.Method) (set : SignalSet) :
    exposed method = some set ↔ Exposes method set := by
  simp only [exposed, Option.bind_eq_some_iff, Exposes, ← SignalNames.read_iff]
  constructor
  · rintro ⟨declared, read, reached, analyzed, checked⟩
    split at checked
    · rename_i same
      cases Option.some.inj checked
      exact ⟨read, same ▸ analyzed⟩
    · contradiction
  · rintro ⟨read, analyzed⟩
    exact ⟨set, read, set, analyzed, by simp⟩

mutual
/-- Bodies of assignments and loops over such bodies: they set no signal. -/
inductive Unsignaled : AST.Statement → Prop where
  | assign : Unsignaled (.assign target value)
  | loop : UnsignaledBody body → Unsignaled (.forLoop binder start stride stop body)

inductive UnsignaledBody : List AST.Statement → Prop where
  | nil : UnsignaledBody []
  | cons : Unsignaled source → UnsignaledBody rest → UnsignaledBody (source :: rest)
end

theorem union_self (set : SignalSet) : set.union set = set :=
  SignalSet.ext fun signal => by simp

mutual
theorem statement_unsignaled (quiet : Unsignaled source) (incoming : SignalSet) :
    statement incoming source = some incoming := by
  cases quiet with
  | assign => rw [statement]
  | loop body =>
    rw [statement, widen, statements_unsignaled body incoming]
    simp [union_self]

theorem statements_unsignaled (quiet : UnsignaledBody sources) (incoming : SignalSet) :
    statements incoming sources = some incoming := by
  cases quiet with
  | nil => rw [statements]
  | cons first rest =>
    rw [statements, statement_unsignaled first incoming]
    exact statements_unsignaled rest incoming
end

/-- A method without an interface whose body sets no signal exposes nothing. -/
theorem exposes_empty (method : AST.Method) (noInterface : method.signals = [])
    (quiet : UnsignaledBody method.body) : Exposes method SignalSet.empty :=
  ⟨⟨[], noInterface, SignalSet.ext fun signal => by simp⟩,
    statements_unsignaled quiet SignalSet.empty⟩

/-- An interface that differs from the reached set is rejected, including an
exposed signal that is never set and a set signal that is not exposed. -/
theorem exposed_rejected (read : SignalNames.read method.signals = some declared)
    (analyzed : statements SignalSet.empty method.body = some reached)
    (different : reached ≠ declared) : exposed method = none := by
  simp [exposed, read, analyzed, different]

theorem closure_rejected (incoming : SignalSet) (closure : AST.Name) (negated : Bool)
    (tested : List AST.Name) (fallback : Option AST.Expr) :
    condition incoming (.signalCheck (some closure) negated tested fallback) = none := rfl

theorem negation_rejected (incoming : SignalSet) (closure : Option AST.Name)
    (tested : List AST.Name) (fallback : Option AST.Expr) :
    condition incoming (.signalCheck closure true tested fallback) = none := by
  cases closure <;> rfl

theorem fallback_rejected (incoming : SignalSet) (closure : Option AST.Name) (negated : Bool)
    (tested : List AST.Name) (fallback : AST.Expr) :
    condition incoming (.signalCheck closure negated tested (some fallback)) = none := by
  cases closure <;> cases negated <;> rfl

theorem unrestricted_rejected (incoming : SignalSet) :
    condition incoming (.signalCheck none false [] none) = none := by
  simp [condition, SignalNames.read, SignalNames.signals, SignalSet.ofList, SignalSet.empty]

/-- §1.4: a tested signal that cannot be set before the check is rejected. -/
theorem untested_rejected {tested : List AST.Name} {testSet incoming : SignalSet}
    (read : SignalNames.read tested = some testSet)
    (outside : ¬ SignalSet.Subset testSet incoming) :
    condition incoming (.signalCheck none false tested none) = none := by
  have notSubset : testSet.subset incoming = false := by
    cases found : testSet.subset incoming
    · rfl
    · exact absurd ((SignalSet.subset_iff _ _).mp found) outside
  simp [condition, read, notSubset]

end Rumoca.GALEC.Elaboration.Reach
