import RumocaCore.GALEC.Names

/-! The six predefined eFMI error signals (eFMI 1.0.0 Beta 1 §3.2.5 §1.1), their
canonical Algorithm Code and manifest spellings, their §1.6 bit positions, and
the encoding of a signal set as the status value returned to the runtime
environment. User-defined signals have no declaration syntax in the admitted
subset, so every signal is predefined. Each spelling is defined here once. -/
namespace Rumoca.GALEC

inductive Signal where
  | invalidArgument
  | overflow
  | nan
  | solveLinearEquationsFailed
  | noSolutionFound
  | unspecifiedError
  deriving Repr, DecidableEq

namespace Signal

/-- Every predefined signal, in §1.6 bit order. -/
def all : List Signal :=
  [invalidArgument, overflow, nan, solveLinearEquationsFailed, noSolutionFound, unspecifiedError]

theorem mem_all (signal : Signal) : signal ∈ all := by
  cases signal <;> simp [all]

/-- The canonical spelling (§1.1; the enumeration of the Algorithm Code
manifest schema). -/
def name : Signal → String
  | invalidArgument => "INVALID_ARGUMENT"
  | overflow => "OVERFLOW"
  | nan => "NAN"
  | solveLinearEquationsFailed => "SOLVE_LINEAR_EQUATIONS_FAILED"
  | noSolutionFound => "NO_SOLUTION_FOUND"
  | unspecifiedError => "UNSPECIFIED_ERROR"

/-- The §1.6 bit position; bits 6 to 15 are reserved and never used. -/
def bit : Signal → Nat
  | invalidArgument => 0
  | overflow => 1
  | nan => 2
  | solveLinearEquationsFailed => 3
  | noSolutionFound => 4
  | unspecifiedError => 5

theorem name_injective {first second : Signal} (same : first.name = second.name) :
    first = second := by
  cases first <;> cases second <;> first | rfl | (simp [name] at same)

theorem bit_lt (signal : Signal) : signal.bit < 6 := by
  cases signal <;> decide

/-- The predefined signal with a spelling, if any. -/
def read (spelling : String) : Option Signal :=
  all.find? fun signal => signal.name == spelling

theorem read_iff (spelling : String) (signal : Signal) :
    read spelling = some signal ↔ signal.name = spelling := by
  constructor
  · intro found
    have matched := List.find?_some found
    simpa using matched
  · intro named
    subst spelling
    cases signal <;> rfl

end Signal

/-- A set of predefined error signals: one membership flag per signal, so set
equality is decidable and computed by the kernel. -/
structure SignalSet where
  invalidArgument : Bool
  overflow : Bool
  nan : Bool
  solveLinearEquationsFailed : Bool
  noSolutionFound : Bool
  unspecifiedError : Bool
  deriving Repr, DecidableEq

namespace SignalSet

def contains (set : SignalSet) : Signal → Bool
  | .invalidArgument => set.invalidArgument
  | .overflow => set.overflow
  | .nan => set.nan
  | .solveLinearEquationsFailed => set.solveLinearEquationsFailed
  | .noSolutionFound => set.noSolutionFound
  | .unspecifiedError => set.unspecifiedError

/-- The set of signals with a membership flag. -/
def ofMembership (member : Signal → Bool) : SignalSet :=
  ⟨member .invalidArgument, member .overflow, member .nan, member .solveLinearEquationsFailed,
    member .noSolutionFound, member .unspecifiedError⟩

@[simp] theorem contains_ofMembership (member : Signal → Bool) (signal : Signal) :
    (ofMembership member).contains signal = member signal := by
  cases signal <;> rfl

theorem ext {first second : SignalSet}
    (same : ∀ signal, first.contains signal = second.contains signal) : first = second := by
  cases first; cases second
  have h0 := same .invalidArgument
  have h1 := same .overflow
  have h2 := same .nan
  have h3 := same .solveLinearEquationsFailed
  have h4 := same .noSolutionFound
  have h5 := same .unspecifiedError
  simp only [contains] at h0 h1 h2 h3 h4 h5
  subst h0 h1 h2 h3 h4 h5
  rfl

def empty : SignalSet := ofMembership fun _ => false

def ofList (signals : List Signal) : SignalSet := ofMembership fun signal => decide (signal ∈ signals)

def union (first second : SignalSet) : SignalSet :=
  ofMembership fun signal => first.contains signal || second.contains signal

/-- The signals of `first` that are not in `second`. -/
def diff (first second : SignalSet) : SignalSet :=
  ofMembership fun signal => first.contains signal && !second.contains signal

@[simp] theorem contains_empty (signal : Signal) : empty.contains signal = false := by
  simp [empty]

@[simp] theorem contains_ofList (signals : List Signal) (signal : Signal) :
    (ofList signals).contains signal = decide (signal ∈ signals) := by
  simp [ofList]

@[simp] theorem contains_union (first second : SignalSet) (signal : Signal) :
    (first.union second).contains signal = (first.contains signal || second.contains signal) := by
  simp [union]

@[simp] theorem contains_diff (first second : SignalSet) (signal : Signal) :
    (first.diff second).contains signal = (first.contains signal && !second.contains signal) := by
  simp [diff]

/-- Some signal belongs to both sets. -/
def Meets (first second : SignalSet) : Prop :=
  ∃ signal, first.contains signal = true ∧ second.contains signal = true

def meets (first second : SignalSet) : Bool :=
  Signal.all.any fun signal => first.contains signal && second.contains signal

theorem meets_iff (first second : SignalSet) : meets first second = true ↔ Meets first second := by
  simp only [meets, List.any_eq_true, Bool.and_eq_true, Meets]
  exact ⟨fun ⟨signal, _, both⟩ => ⟨signal, both⟩,
    fun ⟨signal, both⟩ => ⟨signal, Signal.mem_all signal, both⟩⟩

def Subset (first second : SignalSet) : Prop :=
  ∀ signal, first.contains signal = true → second.contains signal = true

def subset (first second : SignalSet) : Bool :=
  Signal.all.all fun signal => !first.contains signal || second.contains signal

theorem subset_iff (first second : SignalSet) : subset first second = true ↔ Subset first second := by
  simp only [subset, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', Subset]
  constructor
  · intro all signal present
    rcases all signal (Signal.mem_all signal) with absent | contained
    · rw [present] at absent; cases absent
    · exact contained
  · intro contained signal _
    cases present : first.contains signal
    · exact Or.inl rfl
    · exact Or.inr (contained signal present)

/-- §1.6 status value: the sum of `2 ^ bit` over the signals of the set. Bits
6 to 15 are never set, since every bit position is below 6. -/
def encode (set : SignalSet) : Nat :=
  Signal.all.foldr (fun signal total => if set.contains signal then 2 ^ signal.bit + total else total) 0

theorem encode_empty : encode empty = 0 := rfl

theorem encode_overflow : encode (ofList [.overflow]) = 2 := rfl

theorem encode_lt (set : SignalSet) : encode set < 2 ^ 6 := by
  obtain ⟨a, b, c, d, e, f⟩ := set
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

theorem encode_eq_zero_iff (set : SignalSet) : encode set = 0 ↔ set = empty := by
  obtain ⟨a, b, c, d, e, f⟩ := set
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

end SignalSet
end Rumoca.GALEC
