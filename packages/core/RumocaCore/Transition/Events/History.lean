import RumocaCore.Transition
import Mathlib.Data.Stream.Init

/-! Finite and infinite observable histories, determined by their finite prefixes.
Every sequence of transition labels has exactly one history. -/
namespace Rumoca.Transition.Events
variable {S T E R : Type}

inductive History (E : Type) where
  | finite (events : List E)
  | infinite (events : Stream' E)

def History.HasPrefix : History E → List E → Prop
  | .finite events, segment => segment <+: events
  | .infinite events, segment => events.take segment.length = segment

/-- A finite or infinite history is uniquely determined by its finite prefixes. -/
theorem History.ext (same : ∀ segment, first.HasPrefix segment ↔ second.HasPrefix segment) :
    first = (second : History E) := by
  cases first with
  | finite a =>
      cases second with
      | finite b =>
          have ab : a <+: b := (same a).mp (by simp [History.HasPrefix])
          have ba : b <+: a := (same b).mpr (by simp [History.HasPrefix])
          exact congrArg History.finite (ab.eq_of_length_le ba.length_le)
      | infinite b =>
          have bad : b.take (a.length + 1) <+: a := (same _).mpr (by simp [History.HasPrefix])
          have bound := bad.length_le
          simp only [Stream'.length_take] at bound
          omega
  | infinite a =>
      cases second with
      | finite b =>
          have bad : a.take (b.length + 1) <+: b := (same _).mp (by simp [History.HasPrefix])
          have bound := bad.length_le
          simp only [Stream'.length_take] at bound
          omega
      | infinite b =>
          apply congrArg History.infinite
          apply Stream'.take_theorem
          intro n
          have matched : b.take (a.take n).length = a.take n :=
            (same (a.take n)).mp (by simp [History.HasPrefix])
          simpa only [Stream'.length_take] using matched.symm

def accumulate (chunks : Nat → List E) : Nat → List E
  | 0 => []
  | n + 1 => accumulate chunks n ++ chunks n

def Records (chunks : Nat → List E) (history : History E) : Prop :=
  ∀ segment, history.HasPrefix segment ↔ ∃ n, segment <+: accumulate chunks n

theorem records_unique (first : Records chunks a) (second : Records chunks b) : a = b :=
  History.ext (fun segment => (first segment).trans (second segment).symm)

theorem accumulate_prefix (chunks : Nat → List E) (ordered : n ≤ m) :
    accumulate chunks n <+: accumulate chunks m := by
  induction ordered with
  | refl => simp
  | @step m ordered ih => exact ih.trans ⟨chunks m, rfl⟩

theorem accumulate_get (chunks : Nat → List E)
    (left : i < (accumulate chunks n).length) (right : i < (accumulate chunks m).length) :
    (accumulate chunks n)[i] = (accumulate chunks m)[i] := by
  rcases Nat.le_total n m with ordered | ordered
  · exact (accumulate_prefix chunks ordered).getElem left
  · exact ((accumulate_prefix chunks ordered).getElem right).symm

/-- Every possible event sequence has an observable history; divergence is
not silently excluded when the number of emitted events is unbounded. -/
theorem records_exists (chunks : Nat → List E) : ∃ history, Records chunks history := by
  classical
  by_cases maximal : ∃ n, ∀ m, (accumulate chunks m).length ≤ (accumulate chunks n).length
  · obtain ⟨n, maximal⟩ := maximal
    have included (m : Nat) : accumulate chunks m <+: accumulate chunks n := by
      rcases Nat.le_total m n with ordered | ordered
      · exact accumulate_prefix chunks ordered
      · have same := (accumulate_prefix chunks ordered).eq_of_length_le (maximal m)
        rw [same]
    refine ⟨.finite (accumulate chunks n), ?_⟩
    intro segment
    constructor
    · intro member
      exact ⟨n, member⟩
    · rintro ⟨m, member⟩
      exact member.trans (included m)
  · have longer : ∀ n, ∃ m, (accumulate chunks n).length < (accumulate chunks m).length := by
      simpa only [not_exists, not_forall, not_le] using maximal
    let indices : Nat → Nat := Nat.rec 0 (fun _ current => Classical.choose (longer current))
    have long (n : Nat) : n ≤ (accumulate chunks (indices n)).length := by
      induction n with
      | zero => omega
      | succ n ih =>
          have growth := Classical.choose_spec (longer (indices n))
          change (accumulate chunks (indices n)).length < (accumulate chunks (indices (n + 1))).length at growth
          omega
    let pick (i : Nat) := indices (i + 1)
    have bound (i : Nat) : i < (accumulate chunks (pick i)).length := long (i + 1)
    let events : Stream' E := fun i => (accumulate chunks (pick i))[i]'(bound i)
    have takeAccum (n : Nat) : events.take (accumulate chunks n).length = accumulate chunks n := by
      apply List.ext_getElem?
      intro i
      by_cases present : i < (accumulate chunks n).length
      · rw [Stream'.getElem?_take present, List.getElem?_eq_getElem present]
        exact congrArg some (accumulate_get chunks (bound i) present)
      · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt present),
          List.getElem?_eq_none (Nat.le_of_not_gt present)]
    refine ⟨.infinite events, ?_⟩
    intro segment
    constructor
    · intro matched
      have contained := Stream'.take_prefix_take_left segment.length
        (accumulate chunks (pick segment.length)).length events (Nat.le_of_lt (bound segment.length))
      rw [takeAccum, show events.take segment.length = segment from matched] at contained
      exact ⟨pick segment.length, contained⟩
    · rintro ⟨n, contained⟩
      have takeEq : (accumulate chunks n).take segment.length = segment := by
        obtain ⟨tail, same⟩ := contained
        rw [← same]
        simp
      rw [← takeAccum n, Stream'.take_take, Nat.min_eq_right contained.length_le] at takeEq
      exact takeEq

end Rumoca.Transition.Events
