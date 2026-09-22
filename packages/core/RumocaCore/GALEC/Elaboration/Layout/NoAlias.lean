import RumocaCore.GALEC.Elaboration.Layout.Base
import Mathlib.Data.List.Nodup

/-! Distinct typed storage slots independently of declaration names. These
proofs concern existing shaped references and supplied roles, not native memory
addresses or method direction policy. No tensor cells are enumerated. -/
namespace Rumoca.GALEC.Elaboration.Layout
open Elaboration Rumoca.Tensor Rumoca.Solve.Tensor

/-- Remove an added input slot; its own head has no predecessor. -/
def unshiftInput (added : Shape) :
    BindingValue (added :: inputs) outputs → Option (BindingValue inputs outputs)
  | ⟨_, .readOnly .here⟩ => none
  | ⟨shape, .readOnly (.there ref)⟩ => some ⟨shape, .readOnly ref⟩
  | ⟨shape, .writable ref⟩ => some ⟨shape, .writable ref⟩

/-- Remove an added writable slot; its own head has no predecessor. -/
def unshiftOutput (added : Shape) :
    BindingValue inputs (added :: outputs) → Option (BindingValue inputs outputs)
  | ⟨shape, .readOnly ref⟩ => some ⟨shape, .readOnly ref⟩
  | ⟨_, .writable .here⟩ => none
  | ⟨shape, .writable (.there ref)⟩ => some ⟨shape, .writable ref⟩

theorem unshiftInput_shift (added : Shape) (value : BindingValue inputs outputs) :
    unshiftInput added (shiftInput added value) = some value := by
  obtain ⟨shape, access⟩ := value
  cases access <;> rfl

theorem unshiftOutput_shift (added : Shape) (value : BindingValue inputs outputs) :
    unshiftOutput added (shiftOutput added value) = some value := by
  obtain ⟨shape, access⟩ := value
  cases access <;> rfl

theorem shiftInput_injective (added : Shape) :
    Function.Injective (shiftInput (inputs := inputs) (outputs := outputs) added) := by
  intro first second equal
  have same := congrArg (unshiftInput added) equal
  rw [unshiftInput_shift, unshiftInput_shift] at same
  exact Option.some.inj same

theorem shiftOutput_injective (added : Shape) :
    Function.Injective (shiftOutput (inputs := inputs) (outputs := outputs) added) := by
  intro first second equal
  have same := congrArg (unshiftOutput added) equal
  rw [unshiftOutput_shift, unshiftOutput_shift] at same
  exact Option.some.inj same

theorem input_here_ne_shift (added : Shape) (value : BindingValue inputs outputs) :
    (⟨added, .readOnly .here⟩ : BindingValue (added :: inputs) outputs) ≠
      shiftInput added value := by
  intro equal
  have same := congrArg (unshiftInput added) equal
  rw [unshiftInput_shift] at same
  cases same

theorem output_here_ne_shift (added : Shape) (value : BindingValue inputs outputs) :
    (⟨added, .writable .here⟩ : BindingValue inputs (added :: outputs)) ≠
      shiftOutput added value := by
  intro equal
  have same := congrArg (unshiftOutput added) equal
  rw [unshiftOutput_shift] at same
  cases same

private theorem values_mapBindings
    (f : BindingValue inputs outputs → BindingValue newInputs newOutputs)
    (table : BindingTable inputs outputs) :
    (mapBindings f table).map Prod.snd = (table.map Prod.snd).map f := by
  simp only [mapBindings, List.map_map, Function.comp_def]

/-- All allocated role-tagged typed slots are distinct, even if source keys
or shapes repeat. This neither permits duplicate declarations nor changes the
binding table's first-match lookup policy. -/
theorem bindings_values_nodup (fields : List Field) :
    ((bindings fields).map Prod.snd).Nodup := by
  induction fields with
  | nil => exact List.nodup_nil
  | cons field rest ih =>
    obtain ⟨declaration, role⟩ := field
    cases role with
    | readOnly =>
      simp only [bindings, List.map_cons, values_mapBindings]
      apply List.nodup_cons.mpr
      refine ⟨?_, List.Nodup.map (shiftInput_injective _) ih⟩
      intro member
      obtain ⟨value, _, same⟩ := List.mem_map.mp member
      exact input_here_ne_shift _ value same.symm
    | writable =>
      simp only [bindings, List.map_cons, values_mapBindings]
      apply List.nodup_cons.mpr
      refine ⟨?_, List.Nodup.map (shiftOutput_injective _) ih⟩
      intro member
      obtain ⟨value, _, same⟩ := List.mem_map.mp member
      exact output_here_ne_shift _ value same.symm

end Rumoca.GALEC.Elaboration.Layout
