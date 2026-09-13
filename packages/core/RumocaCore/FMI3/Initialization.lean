import RumocaCore.FMI3.Time

/-! Initialization admission for the finite unit profile, independent of C.
The start and enabled stop are finite; the stop is an inclusive bound. The
profile has no internal tolerance-controlled algorithm, so tolerance is unused.
Undefined optional arguments retain arbitrary encodings. This implements the
reviewed profile for FMI 3.0.2 §2.3.2; it is not a rule for every ME/CS solver. -/
namespace Rumoca.FMI3.Initialization
open Binary64 (toBits)

structure Arguments where
  start : Binary64.Value
  toleranceDefined : Bool
  tolerance : BitVec 64
  stopDefined : Bool
  stop : BitVec 64

def Arguments.stopTime (args : Arguments) : Option Binary64.Value :=
  if args.stopDefined then
    match Rumoca.Float64.decode args.stop with
    | .finite value => some value
    | _ => none
  else none

def finiteBits (bits : BitVec 64) : Bool :=
  decide (bits.toNat % Binary64.signPlace < Binary64.magnitudeCount)

/-- An enabled finite stop is an inclusive upper bound on time. -/
def AtLeast (bits : BitVec 64) (lower : Binary64.Value) : Prop :=
  ∃ value : Binary64.Value, (toBits value).val = bits ∧
    Binary64.value lower ≤ Binary64.value value

def atLeast (bits : BitVec 64) (lower : Binary64.Value) : Bool :=
  finiteBits bits && !Rumoca.Float64.test .lt bits (toBits lower).val

theorem atLeast_iff (bits : BitVec 64) (lower : Binary64.Value) :
    atLeast bits lower = true ↔ AtLeast bits lower := by
  constructor
  · intro h
    obtain ⟨hf, ht⟩ := Bool.and_eq_true_iff.mp h
    have hbits : bits.toNat % Binary64.signPlace < Binary64.magnitudeCount := of_decide_eq_true hf
    let value := Binary64.ofBits ⟨bits, hbits⟩
    have hv : (toBits value).val = bits :=
      congrArg Subtype.val (Binary64.toBits_ofBits ⟨bits, hbits⟩)
    refine ⟨value, hv, ?_⟩
    rw [← hv] at ht
    have htest : Rumoca.Float64.test .lt (toBits value).val (toBits lower).val = false := by simpa using ht
    exact le_of_not_gt ((Rumoca.Float64.test_finite_false .lt value lower).mp htest)
  · rintro ⟨value, rfl, hv⟩
    have ht : Rumoca.Float64.test .lt (toBits value).val (toBits lower).val = false :=
      (Rumoca.Float64.test_finite_false .lt value lower).mpr (not_lt.mpr hv)
    simp [atLeast, finiteBits, (toBits value).property, ht]

/-- The fixed unit profile has no internal tolerance-controlled algorithm.
Only an enabled stop restricts the finite initialization time. -/
def Arguments.Admissible (args : Arguments) : Prop :=
  args.stopDefined = true → AtLeast args.stop args.start

theorem equal_stop_admissible (start : Binary64.Value) (toleranceDefined : Bool)
    (tolerance : BitVec 64) :
    Arguments.Admissible ⟨start, toleranceDefined, tolerance, true, (toBits start).val⟩ := by
  intro _
  exact ⟨start, rfl, le_refl _⟩

theorem undefined_stop_admissible (start : Binary64.Value) (toleranceDefined : Bool)
    (tolerance stop : BitVec 64) : Arguments.Admissible ⟨start, toleranceDefined, tolerance, false, stop⟩ := by
  simp [Arguments.Admissible]

theorem tolerance_irrelevant (args : Arguments) (defined : Bool) (bits : BitVec 64) :
    Arguments.Admissible { args with toleranceDefined := defined, tolerance := bits } ↔ Arguments.Admissible args := Iff.rfl

theorem stopTime_defined (args : Arguments) (ha : Arguments.Admissible args) :
    args.stopTime.isSome = args.stopDefined := by
  cases hd : args.stopDefined with
  | false => simp [Arguments.stopTime, hd]
  | true =>
    obtain ⟨value, hv, _⟩ := ha hd
    simp [Arguments.stopTime, hd, ← hv]

theorem stopTime_bits (args : Arguments) (ha : Arguments.Admissible args)
    (value : Binary64.Value) (hs : args.stopTime = some value) : (toBits value).val = args.stop := by
  cases hd : args.stopDefined with
  | false => simp [Arguments.stopTime, hd] at hs
  | true =>
    obtain ⟨bound, hb, _⟩ := ha hd
    have hv : bound = value := by simpa [Arguments.stopTime, hd, ← hb] using hs
    simpa [hv] using hb

end Rumoca.FMI3.Initialization
