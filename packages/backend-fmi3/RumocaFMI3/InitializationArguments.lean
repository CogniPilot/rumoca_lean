import RumocaFMI3.InitializationEntry
import RumocaC.BodyEvents

namespace Rumoca.FMI3.InitializationCalls
open Initialization
open CTree CMemory CBody
open Binary64 (toBits)

/-- All actual Float64 arguments, including nonfinite start values that must
be rejected. Optional unused arguments retain arbitrary bits. -/
structure Raw where
  start : BitVec 64
  toleranceDefined : Bool
  tolerance : BitVec 64
  stopDefined : Bool
  stop : BitVec 64

def Raw.ofFinite (args : Initialization.Arguments) : Raw :=
  ⟨(toBits args.start).val, args.toleranceDefined, args.tolerance, args.stopDefined, args.stop⟩

def rejects (args : Raw) : Bool :=
  !Initialization.finiteBits args.start ||
    (args.stopDefined && (!Initialization.finiteBits args.stop || Rumoca.Float64.test .lt args.stop args.start))

theorem rejects_finite (args : Initialization.Arguments) :
    rejects (Raw.ofFinite args) = (args.stopDefined && !atLeast args.stop args.start) := by
  have valid : Initialization.finiteBits (toBits args.start).val = true := by
    simp [Initialization.finiteBits, (toBits args.start).property]
  simp only [rejects, Raw.ofFinite, valid]
  cases hf : Initialization.finiteBits args.stop <;>
    cases ht : Rumoca.Float64.test .lt args.stop (toBits args.start).val <;>
    simp [atLeast, hf, ht]

theorem finite_admissible (args : Initialization.Arguments) :
    rejects (Raw.ofFinite args) = false ↔ Arguments.Admissible args := by
  rw [rejects_finite]
  simp [Arguments.Admissible, ← atLeast_iff, Bool.and_eq_false_imp]

/-- Independent complete admission: a finite initial time and an optional
finite inclusive stop. Tolerance values do not participate in this policy. -/
theorem rejects_iff (args : Raw) :
    rejects args = false ↔ ∃ finite : Initialization.Arguments, args = Raw.ofFinite finite ∧ Arguments.Admissible finite := by
  constructor
  · intro accepted
    have hf : Initialization.finiteBits args.start = true := by
      have := (Bool.or_eq_false_iff.mp accepted).1
      simpa using this
    have bitsFinite : args.start.toNat % Binary64.signPlace < Binary64.magnitudeCount := of_decide_eq_true hf
    let start := Binary64.ofBits ⟨args.start, bitsFinite⟩
    have bits : (toBits start).val = args.start :=
      congrArg Subtype.val (Binary64.toBits_ofBits ⟨args.start, bitsFinite⟩)
    let finite : Initialization.Arguments := ⟨start, args.toleranceDefined, args.tolerance, args.stopDefined, args.stop⟩
    have encoded : args = Raw.ofFinite finite := by
      dsimp [finite, Raw.ofFinite]
      rw [bits]
    refine ⟨finite, encoded, (finite_admissible finite).mp ?_⟩
    rwa [← encoded]
  · rintro ⟨finite, rfl, accepted⟩
    exact (finite_admissible finite).mpr accepted

def signature : Signature :=
  ⟨"fmi3Status", "fmi3EnterInitializationMode",
    [⟨"fmi3Instance", "instance", false⟩,
     ⟨"fmi3Boolean", "toleranceDefined", false⟩,
     ⟨"fmi3Float64", "tolerance", false⟩,
     ⟨"fmi3Float64", "startTime", false⟩,
     ⟨"fmi3Boolean", "stopTimeDefined", false⟩,
     ⟨"fmi3Float64", "stopTime", false⟩]⟩

def arguments (handle : Option Address) (args : Raw) : List Value :=
  [.pointer handle, boolean args.toleranceDefined, .float64 args.tolerance,
   .float64 args.start, boolean args.stopDefined, .float64 args.stop]

def parameters (handle : Option Address) (args : Raw) : Locals :=
  CBody.bind (CBody.bind (CBody.bind (CBody.bind (CBody.bind (CBody.bind (fun _ => none)
    "stopTime" (.float64 args.stop)) "stopTimeDefined" (boolean args.stopDefined))
    "startTime" (.float64 args.start)) "tolerance" (.float64 args.tolerance))
    "toleranceDefined" (boolean args.toleranceDefined)) "instance" (.pointer handle)

def locals (p : Address) (args : Raw) : Locals :=
  CBody.bind (parameters (some p) args) "m" (.pointer (some p))

/-- Initialization guard for the existing unit profile. -/
def guard : Expr := Runtime.any [Runtime.negate (Runtime.finite (Runtime.v "startTime")),
  Runtime.both (Runtime.v "stopTimeDefined")
    (Runtime.either (Runtime.negate (Runtime.finite (Runtime.v "stopTime")))
      (Runtime.lt (Runtime.v "stopTime") (Runtime.v "startTime")))]

section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

theorem parameters_bound (handle : Option Address) (args : Raw) :
    CCalls.parameters signature.parameters (arguments handle args) = some (parameters handle args) := by
  cases ht : args.toleranceDefined <;> cases hs : args.stopDefined <;>
    simp [signature, arguments, CCalls.parameters, CCalls.parameterType, parameters,
      CBody.bind, CBody.cast, convert, boolean, Value.truth, ht, hs]

omit static in
theorem finite_parameters (p : Address) (args : Initialization.Arguments) :
    parameters (some p) (Raw.ofFinite args) = InitializationEntry.parameters p args := by
  funext name
  simp [parameters, Raw.ofFinite, InitializationEntry.parameters, CBody.bind, Value.finite]
  split_ifs <;> simp_all

theorem guard_eval (heap : Heap) (p : Address) (args : Raw) :
    CBody.eval (locals p args) heap guard = some (boolean (rejects args)) := by
  have startFinite : Value.isFinite (.float64 args.start) = some (Initialization.finiteBits args.start) := rfl
  have stopFinite : Value.isFinite (.float64 args.stop) = some (Initialization.finiteBits args.stop) := rfl
  simp [guard, Runtime.any, Runtime.either, Runtime.both, Runtime.negate,
    Runtime.finite, Runtime.call, Runtime.lt, Runtime.v, Runtime.n, CBody.eval,
    locals, parameters, CBody.bind, resolve, constants, comparison, floatComparison,
    convert, startFinite, stopFinite, rejects]
  all_goals
    cases hd : args.stopDefined <;>
      cases hf : Initialization.finiteBits args.start <;>
      cases hs : Initialization.finiteBits args.stop <;>
      cases hc : Rumoca.Float64.test .lt args.stop args.start <;>
      simp_all [boolean, Value.truth]

end
end Rumoca.FMI3.InitializationCalls
