import RumocaCore.GALEC.Elaboration.Capabilities.Generic

/-! Value-preserving partitions of the existing whole-shaped environment.
Traversal is over declarations, never tensor cells. Roles remain preparation
parameters, not callbacks in a target IR; no source policy is licensed here. -/
namespace Rumoca.GALEC.Elaboration.Layout.State
open Rumoca.Tensor Rumoca.Solve.Tensor
def shapes : List Layout.Field → List Shape
  | [] => []
  | field :: rest => field.declaration.shape :: shapes rest

def readOnly : (fields : List Layout.Field) → Env α (shapes fields) →
      Env α (Layout.inputShapes fields)
  | [], _ => Env.empty
  | ⟨_, .readOnly⟩ :: rest, state =>
      Env.push (state .here) (readOnly rest (fun ref => state (.there ref)))
  | ⟨_, .writable⟩ :: rest, state => readOnly rest (fun ref => state (.there ref))

def writable : (fields : List Layout.Field) → Env α (shapes fields) →
      Env α (Layout.outputShapes fields)
  | [], _ => Env.empty
  | ⟨_, .readOnly⟩ :: rest, state => writable rest (fun ref => state (.there ref))
  | ⟨_, .writable⟩ :: rest, state =>
      Env.push (state .here) (writable rest (fun ref => state (.there ref)))

def join : (fields : List Layout.Field) → Env α (Layout.inputShapes fields) →
      Env α (Layout.outputShapes fields) → Env α (shapes fields)
  | [], _, _ => Env.empty
  | ⟨_, .readOnly⟩ :: rest, input, output =>
      Env.push (input .here) (join rest (fun ref => input (.there ref)) @output)
  | ⟨_, .writable⟩ :: rest, input, output =>
      Env.push (output .here) (join rest @input (fun ref => output (.there ref)))

theorem join_partition (fields : List Layout.Field) (state : Env α (shapes fields)) :
    @join α fields (readOnly fields @state) (writable fields @state) = @state := by
  induction fields with
  | nil => funext shape ref; cases ref
  | cons field rest ih =>
    obtain ⟨declaration, role⟩ := field
    cases role <;> simp only [join, readOnly, writable]
    all_goals
      funext shape ref
      cases ref with
      | here => rfl
      | there ref => exact congrFun (congrFun (ih (fun ref => state (.there ref))) shape) ref

theorem readOnly_join (fields : List Layout.Field)
    (input : Env α (Layout.inputShapes fields)) (output : Env α (Layout.outputShapes fields)) :
    @readOnly α fields (join fields @input @output) = @input := by
  induction fields with
  | nil => funext shape ref; cases ref
  | cons field rest ih =>
    obtain ⟨declaration, role⟩ := field
    cases role with
    | readOnly =>
      funext shape ref
      cases ref with
      | here => rfl
      | there ref =>
        exact congrFun (congrFun (ih (fun ref => input (.there ref)) @output) shape) ref
    | writable => exact ih @input (fun ref => output (.there ref))

theorem writable_join (fields : List Layout.Field)
    (input : Env α (Layout.inputShapes fields)) (output : Env α (Layout.outputShapes fields)) :
    @writable α fields (join fields @input @output) = @output := by
  induction fields with
  | nil => funext shape ref; cases ref
  | cons field rest ih =>
    obtain ⟨declaration, role⟩ := field
    cases role with
    | readOnly => exact ih (fun ref => input (.there ref)) @output
    | writable =>
      funext shape ref
      cases ref with
      | here => rfl
      | there ref =>
        exact congrFun (congrFun (ih @input (fun ref => output (.there ref))) shape) ref

theorem join_injective (fields : List Layout.Field)
    (input otherInput : Env α (Layout.inputShapes fields))
    (output otherOutput : Env α (Layout.outputShapes fields)) :
    @join α fields @input @output = @join α fields @otherInput @otherOutput ↔
      @input = @otherInput ∧ @output = @otherOutput := by
  constructor
  · intro same
    constructor
    · simpa only [readOnly_join] using congrArg (@readOnly α fields) same
    · simpa only [writable_join] using congrArg (@writable α fields) same
  · rintro ⟨rfl, rfl⟩
    rfl

theorem shapes_declarations (fields : List Layout.Field) :
    shapes fields = (fields.map Layout.Field.declaration).map Declarations.Real.Descriptor.shape := by
  induction fields with
  | nil => rfl
  | cons field rest ih => simp only [shapes, List.map_cons, ih]

/-- Alignment uses every ordered descriptor, not shape equality alone. -/
theorem shapes_aligned (same : left.map Layout.Field.declaration = right.map Layout.Field.declaration) :
    shapes left = shapes right := by
  rw [shapes_declarations, same, shapes_declarations]

def castEnv (same : source = target) (state : Env α source) : Env α target := same ▸ state

theorem castEnv_refl (state : Env α context) : @castEnv context context α rfl @state = @state := rfl

theorem castEnv_trans (first : a = b) (second : b = c) (state : Env α a) :
    @castEnv b c α second (castEnv first @state) = @castEnv a c α (first.trans second) @state := by
  cases first
  cases second
  rfl

/-- Repartition complete values while preserving the original ordered
declarations. Equal-shaped but differently named fields cannot be swapped. -/
def repartition (same : left.map Layout.Field.declaration = right.map Layout.Field.declaration)
    (input : Env α (Layout.inputShapes left)) (output : Env α (Layout.outputShapes left)) :
    (Env α (Layout.inputShapes right)) × (Env α (Layout.outputShapes right)) :=
  let state : Env α (shapes right) := castEnv (shapes_aligned same) (join left @input @output)
  ⟨readOnly right @state, writable right @state⟩

theorem repartition_preserves
    (same : left.map Layout.Field.declaration = right.map Layout.Field.declaration)
    (input : Env α (Layout.inputShapes left)) (output : Env α (Layout.outputShapes left)) :
    @join α right (repartition same @input @output).1 (repartition same @input @output).2 =
      @castEnv (shapes left) (shapes right) α (shapes_aligned same) (join left @input @output) :=
  join_partition right _

theorem repartition_identity (fields : List Layout.Field)
    (input : Env α (Layout.inputShapes fields)) (output : Env α (Layout.outputShapes fields)) :
    repartition (left := fields) (right := fields) rfl @input @output = (@input, @output) := by
  apply Prod.ext
  · exact readOnly_join fields @input @output
  · exact writable_join fields @input @output

theorem repartition_trans {left middle right : List Layout.Field}
    (first : left.map Layout.Field.declaration = middle.map Layout.Field.declaration)
    (second : middle.map Layout.Field.declaration = right.map Layout.Field.declaration)
    (input : Env α (Layout.inputShapes left)) (output : Env α (Layout.outputShapes left)) :
    repartition second (repartition first @input @output).1 (repartition first @input @output).2 =
      repartition (first.trans second) @input @output := by
  simp only [repartition, join_partition, castEnv_trans]

theorem repartition_inverse {left right : List Layout.Field}
    (same : left.map Layout.Field.declaration = right.map Layout.Field.declaration)
    (input : Env α (Layout.inputShapes left)) (output : Env α (Layout.outputShapes left)) :
    repartition same.symm (repartition same @input @output).1 (repartition same @input @output).2 =
      (@input, @output) := by
  simpa only [repartition_identity] using repartition_trans same same.symm @input @output

/-- A transported pair is exactly the unique pair representing the same
complete ordered state, not merely equal output observations. -/
theorem repartition_iff
    (same : left.map Layout.Field.declaration = right.map Layout.Field.declaration)
    (input : Env α (Layout.inputShapes left)) (output : Env α (Layout.outputShapes left))
    (nextInput : Env α (Layout.inputShapes right)) (nextOutput : Env α (Layout.outputShapes right)) :
    repartition same @input @output = (@nextInput, @nextOutput) ↔
      @join α right @nextInput @nextOutput =
        @castEnv (shapes left) (shapes right) α (shapes_aligned same) (join left @input @output) := by
  constructor
  · intro samePair
    have preserved := repartition_preserves same @input @output
    rw [samePair] at preserved
    exact preserved
  · intro preserved
    have sameJoined := (repartition_preserves same @input @output).trans preserved.symm
    obtain ⟨sameInput, sameOutput⟩ := (join_injective right _ _ _ _).mp sameJoined
    exact Prod.ext sameInput sameOutput

end Rumoca.GALEC.Elaboration.Layout.State
