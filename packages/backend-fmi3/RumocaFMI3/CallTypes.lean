import RumocaFMI3.LiteralPreparation
import RumocaC.CallSignature
import RumocaC.UnsignedMemory

/-! Parameter and return-type coverage for the actual rendered function list.
Pointer bindings represent opaque addresses, not pointee layout or callback
execution. Call entry preserves the heap and constructs a fresh, typed scope;
complete body behavior and native header/ABI correspondence remain separate. -/
noncomputable section
namespace Rumoca.FMI3.CallTypes
open CTree CMemory LiteralPreparation

theorem helpers_ready (literals : CLiteralAddresses) (fn : Function)
    (member : fn ∈ Runtime.helpers) : @CCalls.Signature.Ready (cInterface literals) fn.signature := by
  change @CCalls.Signature.Ready cInterface fn.signature
  simp [Runtime.helpers] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide +kernel

theorem functions_ready (m : Solve.FMI3Model source) (sigs : List Signature)
    (known : ∀ sig ∈ sigs, @CCalls.Signature.Ready cInterface sig)
    (literals : CLiteralAddresses) :
    ∀ fn ∈ functions m sigs, @CCalls.Signature.Ready (cInterface literals) fn.signature := by
  intro fn member
  change fn ∈ Runtime.helpers ++ sigs.map (Runtime.function m) at member
  rcases List.mem_append.mp member with helper | exported
  · exact helpers_ready literals fn helper
  · obtain ⟨sig, sigMember, rfl⟩ := List.mem_map.mp exported
    exact known sig sigMember

/-- The selected value-reference meaning is unsigned 32-bit conversion,
including out-of-range integers. This is not a typedef/header parsing proof. -/
theorem value_reference_conversion (literals : CLiteralAddresses) (input output : Int) :
    @CBody.cast (cInterface literals) "fmi3ValueReference" (.integer input) =
      some (.integer output) ↔ CUnsigned.Converts 32 input output := by
  change convert (.unsigned 32) (.integer input) = some (.integer output) ↔ _
  exact convert_unsigned_iff 32 input output

theorem value_reference_bits (literals : CLiteralAddresses) (input : Int) :
    @CBody.cast (cInterface literals) "fmi3ValueReference" (.integer input) =
      some (.integer ((BitVec.ofInt 32 input).toNat : Int)) := by
  change convert (.unsigned 32) (.integer input) = _
  exact convert_unsigned_bits 32 input

theorem entry (m : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((functions m sigs).map (fun fn => fn.signature.name)).Nodup)
    (known : ∀ fn ∈ functions m sigs, @CCalls.Signature.Ready cInterface fn.signature)
    (literals : CLiteralAddresses) (fn : Function) (member : fn ∈ functions m sigs)
    (arguments : @CCalls.Signature.Arguments (cInterface literals) fn.signature.parameters inputs outputs)
    (heap : Heap) (stack : CCalls.Typed.Continuation) :
    ∃ types,
      @CCalls.Typed.next (cInterface literals) (program m sigs)
        (.calling fn.signature.name inputs heap stack) =
        some (.body (.running fn.body (CCalls.Signature.locals fn.signature.parameters outputs) types heap)
          fn.signature.result stack) ∧
      CCalls.Parameters.Coherent (CCalls.Signature.locals fn.signature.parameters outputs) types :=
  CCalls.Signature.call_entry (interface := cInterface literals) (fn := fn) (known fn member) arguments
    (program m sigs) heap stack (definition_bound m sigs unique fn member)

theorem arguments_exist (m : Solve.FMI3Model source) (sigs : List Signature)
    (known : ∀ fn ∈ functions m sigs, @CCalls.Signature.Ready cInterface fn.signature)
    (literals : CLiteralAddresses) (fn : Function) (member : fn ∈ functions m sigs) :
    ∃ values, @CCalls.Signature.Arguments (cInterface literals) fn.signature.parameters values values :=
  CCalls.Signature.arguments_exist (interface := cInterface literals) (known fn member).2.1

end Rumoca.FMI3.CallTypes
