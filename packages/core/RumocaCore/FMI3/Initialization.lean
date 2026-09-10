import RumocaCore.FMI3.Time

/-! Initialization parameters for the existing finite unit profile, independent
of the C adapter. Enabled tolerance must be finite and positive; enabled stop
must be finite and strictly later than start. These are the current runtime's
admission restrictions, not a claim that FMI 3.0.2 requires these exact strict
inequalities. Undefined arguments retain arbitrary bits, including NaNs.
Review against §2.3.2 and complete error/lifetime conformance remain separate. -/
namespace Rumoca.FMI3.Initialization
open Binary64 (toBits)

structure Arguments where
  start : Binary64.Value
  toleranceDefined : Bool
  tolerance : BitVec 64
  stopDefined : Bool
  stop : BitVec 64

def Above (bits : BitVec 64) (lower : Binary64.Value) : Prop :=
  ∃ value : Binary64.Value, (toBits value).val = bits ∧
    Binary64.value lower < Binary64.value value

def Arguments.Admissible (args : Arguments) : Prop :=
  (args.toleranceDefined = true → Above args.tolerance Binary64.positiveZero) ∧
  (args.stopDefined = true → Above args.stop args.start)

def Arguments.stopTime (args : Arguments) : Option Binary64.Value :=
  if args.stopDefined then
    match Rumoca.Float64.decode args.stop with
    | .finite value => some value
    | _ => none
  else none

theorem stopTime_defined (args : Arguments) (ha : args.Admissible) :
    args.stopTime.isSome = args.stopDefined := by
  cases hd : args.stopDefined with
  | false => simp [Arguments.stopTime, hd]
  | true =>
    obtain ⟨value, hv, _⟩ := ha.2 hd
    simp [Arguments.stopTime, hd, ← hv]

theorem stopTime_bits (args : Arguments) (ha : args.Admissible) (value : Binary64.Value)
    (hs : args.stopTime = some value) : (toBits value).val = args.stop := by
  cases hd : args.stopDefined with
  | false => simp [Arguments.stopTime, hd] at hs
  | true =>
    obtain ⟨bound, hb, _⟩ := ha.2 hd
    have hv : bound = value := by simpa [Arguments.stopTime, hd, ← hb] using hs
    simpa [hv] using hb

def finiteBits (bits : BitVec 64) : Bool :=
  decide (bits.toNat % Binary64.signPlace < Binary64.magnitudeCount)

def above (bits : BitVec 64) (lower : Binary64.Value) : Bool :=
  finiteBits bits && !Rumoca.Float64.test .le bits (toBits lower).val

theorem above_iff (bits : BitVec 64) (lower : Binary64.Value) :
    above bits lower = true ↔ Above bits lower := by
  constructor
  · intro h
    obtain ⟨hf, ht⟩ := Bool.and_eq_true_iff.mp h
    have hbits : bits.toNat % Binary64.signPlace < Binary64.magnitudeCount :=
      of_decide_eq_true hf
    let value := Binary64.ofBits ⟨bits, hbits⟩
    have hv : (toBits value).val = bits :=
      congrArg Subtype.val (Binary64.toBits_ofBits ⟨bits, hbits⟩)
    refine ⟨value, hv, ?_⟩
    rw [← hv] at ht
    have htest : Rumoca.Float64.test .le (toBits value).val (toBits lower).val = false :=
      by simpa using ht
    exact lt_of_not_ge ((Rumoca.Float64.test_finite_false .le value lower).mp htest)
  · rintro ⟨value, rfl, hv⟩
    have ht : Rumoca.Float64.test .le (toBits value).val (toBits lower).val = false :=
      (Rumoca.Float64.test_finite_false .le value lower).mpr (not_le.mpr hv)
    simp [above, finiteBits, (toBits value).property, ht]

end Rumoca.FMI3.Initialization
