import RumocaFMI3.DeclaredMetadata
import RumocaFMI3.Float64Dispatch
import RumocaFMI3.RuntimePrinter
import RumocaFMI3.TensorInstanceStorage
import RumocaC.CallPolicy

/-! Float64 accessor dispatch tables built from the declared interface.

The value references are those of the model description
(`DeclaredMetadata.table`). This module adds the C record stage: the instance
record keeps the declarations of each role in one contiguous `double` block
(inputs in `u`, states in `x` with their derivatives at the same offsets in
`dx`, algebraic outputs in `J`), and the time base in the scalar `time`. A
declaration's element offset in its block is the total volume of the preceding
declarations of the same role, and its element count is its own volume. The
getter reads every reference, evaluating a calculated variable (a state
derivative or an algebraic output) first through the profile's kernel entries
(`Reads`); the setter writes inputs and states, whose start values are exact. The accessor bodies (`TensorFloat64.getFunction`,
`TensorFloat64.setFunction`) dispatch over these arms for every profile. -/
noncomputable section
namespace Rumoca.FMI3.Float64Table
open CTree Rumoca.Solve Rumoca.FMI3.DeclaredMetadata

/-- The part of the instance record one value reference addresses. -/
structure Region where
  member : String
  offset : Nat
  count : Nat
  deriving Repr, DecidableEq

/-- The record regions of the table entries, given the element offsets already
used in the input, state and output blocks. A state's derivative directly
follows it in the table and shares its offset; the state block advances after
the derivative. -/
def regions (inputs states outputs : Nat) : List Entry → List (Entry × Region)
  | [] => []
  | e :: es =>
    match e.target with
    | .value d =>
      match d.role with
      | .input => (e, ⟨TensorInstance.inputName, inputs, d.shape.volume⟩) ::
          regions (inputs + d.shape.volume) states outputs es
      | .state => (e, ⟨TensorInstance.stateName, states, d.shape.volume⟩) :: regions inputs states outputs es
      | .algebraic => (e, ⟨TensorInstance.outputName, outputs, d.shape.volume⟩) ::
          regions inputs states (outputs + d.shape.volume) es
    | .derivative d _ => (e, ⟨TensorInstance.derivativeName, states, d.shape.volume⟩) ::
        regions inputs (states + d.shape.volume) outputs es

/-- The record regions of an interface's value references. -/
def recordRegions (i : Interface) : List (Entry × Region) := regions 0 0 0 (table i)

/-- The staged pointer to the first element of a region: the scalar time base is
`&(m->time)`, every other region `&(m->member)[offset]`. -/
def pointer (member : String) (offset : Nat) : Expr :=
  if member = TensorInstance.timeName then .address (Runtime.field member)
  else .address (.index (Runtime.field member) (Runtime.n offset))

/-- A getter arm stages the region pointer and its element count. -/
def getArm (r : Region) : List Stmt :=
  [.assign (Runtime.v "src") (pointer r.member r.offset), .assign (Runtime.v "expected") (Runtime.n r.count)]

/-- A setter arm stages the writable region pointer and its element count. -/
def setArm (r : Region) : List Stmt :=
  [.assign (Runtime.v "dst") (pointer r.member r.offset), .assign (Runtime.v "expected") (Runtime.n r.count)]

/-- The independent time base, reference `0`. -/
def timeRegion : Region := ⟨TensorInstance.timeName, 0, 1⟩

/-- A reference the host may write: an input, or a state whose start is exact. -/
def Entry.writable (e : Entry) : Bool :=
  match e.target with
  | .value d => d.role == .input || d.role == .state
  | .derivative _ _ => false

/-- The evaluations the getter runs before staging a calculated variable: the
profile's prepared kernel entries computing the state derivatives and the
algebraic outputs from the current inputs and states. -/
structure Reads where
  derivative : List Stmt
  output : List Stmt

/-- The statements a getter arm runs for one table entry: a calculated variable
is evaluated first, then its region is staged. -/
def Reads.arm (reads : Reads) (e : Entry) (r : Region) : List Stmt :=
  match e.target with
  | .derivative _ _ => reads.derivative ++ getArm r
  | .value d =>
    match d.role with
    | .algebraic => reads.output ++ getArm r
    | _ => getArm r

/-- The getter arms: the time base, then every table reference. -/
def getArms (reads : Reads) (i : Interface) : List (Nat × List Stmt) :=
  (0, getArm timeRegion) :: (recordRegions i).map fun (e, r) => (e.reference, reads.arm e r)

/-- The setter arms: the writable table references. -/
def setArms (i : Interface) : List (Nat × List Stmt) :=
  ((recordRegions i).filter fun (e, _) => Entry.writable e).map fun (e, r) => (e.reference, setArm r)

/-! ### The dispatch references are the declared value references -/

theorem regions_entries (inputs states outputs : Nat) (es : List Entry) :
    (regions inputs states outputs es).map Prod.fst = es := by
  induction es generalizing inputs states outputs with
  | nil => rfl
  | cons e es ih =>
    unfold regions
    split
    · split <;> simp [ih]
    · simp [ih]

/-- The getter dispatches over exactly the value references of the model
description, in `ModelVariables` order. -/
theorem getArms_references (reads : Reads) (i : Interface) :
    (getArms reads i).map Prod.fst = DeclaredMetadata.valueReferences i := by
  have entries := regions_entries 0 0 0 (table i)
  simp only [getArms, List.map_cons, List.map_map, DeclaredMetadata.valueReferences]
  congr 1
  rw [← entries, List.map_map]
  rfl

/-- The setter dispatches over exactly the references of the declared inputs and
states. -/
theorem setArms_references (i : Interface) :
    (setArms i).map Prod.fst = ((table i).filter Entry.writable).map Entry.reference := by
  have entries := regions_entries 0 0 0 (table i)
  simp only [setArms, recordRegions, List.map_map]
  conv_rhs => rw [← entries, List.filter_map, List.map_map]
  rfl

/-! ### Printed-text denotation -/

section
open CTree.Printer CTree.Syntax

theorem regions_member (inputs states outputs : Nat) (es : List Entry) :
    ∀ a ∈ regions inputs states outputs es,
      a.2.member ∈ [TensorInstance.inputName, TensorInstance.stateName, TensorInstance.derivativeName, TensorInstance.outputName] := by
  induction es generalizing inputs states outputs with
  | nil => intro a ha; cases ha
  | cons e es ih =>
    intro a ha
    unfold regions at ha
    split at ha
    · split at ha <;> rcases List.mem_cons.mp ha with rfl | ha <;>
        first | (simp; done) | exact ih _ _ _ a ha
    · rcases List.mem_cons.mp ha with rfl | ha
      · simp
      · exact ih _ _ _ a ha

theorem pointer_printable (member : String) (offset : Nat)
    (hv : CIdentifier.valid [] member = true) :
    Printable RuntimePrinter.typedefs (pointer member offset) := by
  simp only [pointer, Runtime.field, Runtime.v, Runtime.n]
  split
  · exact Printable.address
      (Printable.field (Printable.identifier (by decide +kernel)) (by simp [Postfix]) (by simp [FieldBase]) hv)
  · exact Printable.address (Printable.index
      (Printable.field (Printable.identifier (by decide +kernel)) (by simp [Postfix]) (by simp [FieldBase]) hv)
      (by simp [Postfix]) Printable.natural)

theorem member_valid (member : String)
    (h : member ∈ [TensorInstance.timeName, TensorInstance.inputName, TensorInstance.stateName, TensorInstance.derivativeName, TensorInstance.outputName]) :
    CIdentifier.valid [] member = true := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem getArm_printable (r : Region)
    (h : r.member ∈ [TensorInstance.timeName, TensorInstance.inputName, TensorInstance.stateName, TensorInstance.derivativeName, TensorInstance.outputName]) :
    ∀ stmt ∈ getArm r, ItemPrintable RuntimePrinter.typedefs stmt := by
  intro stmt hs
  simp only [getArm, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact ItemPrintable.assign (Printable.identifier (by decide +kernel))
      (pointer_printable _ _ (member_valid _ h))
  · exact ItemPrintable.assign (Printable.identifier (by decide +kernel)) Printable.natural

theorem setArm_printable (r : Region)
    (h : r.member ∈ [TensorInstance.timeName, TensorInstance.inputName, TensorInstance.stateName, TensorInstance.derivativeName, TensorInstance.outputName]) :
    ∀ stmt ∈ setArm r, ItemPrintable RuntimePrinter.typedefs stmt := by
  intro stmt hs
  simp only [setArm, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact ItemPrintable.assign (Printable.identifier (by decide +kernel))
      (pointer_printable _ _ (member_valid _ h))
  · exact ItemPrintable.assign (Printable.identifier (by decide +kernel)) Printable.natural

private theorem record_member (i : Interface) (a : Entry × Region) (ha : a ∈ recordRegions i) :
    a.2.member ∈ [TensorInstance.timeName, TensorInstance.inputName, TensorInstance.stateName, TensorInstance.derivativeName, TensorInstance.outputName] :=
  List.mem_cons_of_mem _ (regions_member 0 0 0 (table i) a ha)

theorem getArms_printable (reads : Reads) (i : Interface)
    (evaluations : ∀ stmt ∈ reads.derivative ++ reads.output, ItemPrintable RuntimePrinter.typedefs stmt) :
    ∀ a ∈ getArms reads i, ∀ stmt ∈ a.2, ItemPrintable RuntimePrinter.typedefs stmt := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact getArm_printable timeRegion (by simp [timeRegion])
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    have staged := getArm_printable b.2 (record_member i b hb)
    intro stmt member
    simp only [Reads.arm] at member
    split at member
    · rcases List.mem_append.mp member with h | h
      · exact evaluations stmt (List.mem_append_left _ h)
      · exact staged stmt h
    · split at member
      · rcases List.mem_append.mp member with h | h
        · exact evaluations stmt (List.mem_append_right _ h)
        · exact staged stmt h
      · exact staged stmt member

theorem setArms_printable (i : Interface) :
    ∀ a ∈ setArms i, ∀ stmt ∈ a.2, ItemPrintable RuntimePrinter.typedefs stmt := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact setArm_printable b.2 (record_member i b (List.mem_filter.mp hb).1)

end

/-! ### Declaration-free arms -/

theorem getArm_noDecl (r : Region) : (getArm r).all CLoops.noDeclarations = true := by
  simp [getArm, CLoops.noDeclarations]

theorem setArm_noDecl (r : Region) : (setArm r).all CLoops.noDeclarations = true := by
  simp [setArm, CLoops.noDeclarations]

theorem getArms_noDecl (reads : Reads) (i : Interface)
    (evaluations : (reads.derivative ++ reads.output).all CLoops.noDeclarations = true) :
    ∀ a ∈ getArms reads i, a.2.all CLoops.noDeclarations = true := by
  intro a ha
  have hd : reads.derivative.all CLoops.noDeclarations = true := by
    simp only [List.all_append, Bool.and_eq_true] at evaluations; exact evaluations.1
  have ho : reads.output.all CLoops.noDeclarations = true := by
    simp only [List.all_append, Bool.and_eq_true] at evaluations; exact evaluations.2
  rcases List.mem_cons.mp ha with rfl | ha
  · exact getArm_noDecl _
  · obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    simp only [Reads.arm]
    split
    · simp [List.all_append, hd, getArm_noDecl]
    · split
      · simp [List.all_append, ho, getArm_noDecl]
      · exact getArm_noDecl _

theorem setArms_noDecl (i : Interface) :
    ∀ a ∈ setArms i, a.2.all CLoops.noDeclarations = true := by
  intro a ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
  exact setArm_noDecl _

/-! ### Calls -/

section
open CCallPolicy

theorem pointer_admits (p : Expr → Prop) (member : String) (offset : Nat) :
    ExpressionAdmits p (pointer member offset) := by
  unfold pointer
  split <;> simp [ExpressionAdmits, Runtime.field, Runtime.v, Runtime.n]

/-- A dispatch arm stages a pointer and a count and calls nothing. -/
theorem getArm_admits (p : Expr → Prop) (r : Region) : ∀ stmt ∈ getArm r, StatementAdmits p stmt := by
  intro stmt hs
  simp only [getArm, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl <;>
    simp [StatementAdmits, ExpressionAdmits, pointer_admits, Runtime.v, Runtime.n]

theorem setArm_admits (p : Expr → Prop) (r : Region) : ∀ stmt ∈ setArm r, StatementAdmits p stmt := by
  intro stmt hs
  simp only [setArm, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl <;>
    simp [StatementAdmits, ExpressionAdmits, pointer_admits, Runtime.v, Runtime.n]

theorem getArms_admits (p : Expr → Prop) (reads : Reads) (i : Interface)
    (evaluations : ∀ stmt ∈ reads.derivative ++ reads.output, StatementAdmits p stmt) :
    ∀ a ∈ getArms reads i, ∀ stmt ∈ a.2, StatementAdmits p stmt := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact getArm_admits p _
  · obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    intro stmt member
    simp only [Reads.arm] at member
    split at member
    · rcases List.mem_append.mp member with h | h
      · exact evaluations stmt (List.mem_append_left _ h)
      · exact getArm_admits p _ stmt h
    · split at member
      · rcases List.mem_append.mp member with h | h
        · exact evaluations stmt (List.mem_append_right _ h)
        · exact getArm_admits p _ stmt h
      · exact getArm_admits p _ stmt member

theorem setArms_admits (p : Expr → Prop) (i : Interface) :
    ∀ a ∈ setArms i, ∀ stmt ∈ a.2, StatementAdmits p stmt := by
  intro a ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
  exact setArm_admits p _

end


/-! ### Every region lies inside its record block -/

/-- The total volume of the declarations of one role. -/
def roleVolume (role : Role) (ds : List Declaration) : Nat :=
  ((ds.filter (·.role == role)).map fun d => d.shape.volume).sum

/-- A region lies inside the record block its member names: the input block,
the state block (shared by the states and their derivatives) or the output
block. -/
def Region.Within (inputs states outputs : Nat) (r : Region) : Prop :=
  (r.member = TensorInstance.inputName → r.offset + r.count ≤ inputs) ∧
  ((r.member = TensorInstance.stateName ∨ r.member = TensorInstance.derivativeName) → r.offset + r.count ≤ states) ∧
  (r.member = TensorInstance.outputName → r.offset + r.count ≤ outputs)

theorem regions_within (inputs states outputs next : Nat) (ds : List Declaration) :
    ∀ a ∈ regions inputs states outputs (entries next ds),
      a.2.Within (inputs + roleVolume .input ds) (states + roleVolume .state ds)
        (outputs + roleVolume .algebraic ds) := by
  induction ds generalizing inputs states outputs next with
  | nil => intro a member; cases member
  | cons d ds ih =>
    intro a member
    have xu : TensorInstance.stateName ≠ TensorInstance.inputName := by decide
    have dxu : TensorInstance.derivativeName ≠ TensorInstance.inputName := by decide
    have ju : TensorInstance.outputName ≠ TensorInstance.inputName := by decide
    have ux : TensorInstance.inputName ≠ TensorInstance.stateName := by decide
    have udx : TensorInstance.inputName ≠ TensorInstance.derivativeName := by decide
    have jx : TensorInstance.outputName ≠ TensorInstance.stateName := by decide
    have jdx : TensorInstance.outputName ≠ TensorInstance.derivativeName := by decide
    have uj : TensorInstance.inputName ≠ TensorInstance.outputName := by decide
    have xj : TensorInstance.stateName ≠ TensorInstance.outputName := by decide
    have dxj : TensorInstance.derivativeName ≠ TensorInstance.outputName := by decide
    cases hr : d.role with
    | input =>
      simp only [entries, hr, regions, List.mem_cons] at member
      rcases member with rfl | member
      · refine ⟨fun _ => ?_, fun h => ?_, fun h => ?_⟩
        · simp [roleVolume, hr]
        · rcases h with h | h
          · exact absurd h ux
          · exact absurd h udx
        · exact absurd h uj
      · have within := ih _ _ _ _ a member
        simpa [roleVolume, hr, Nat.add_assoc] using within
    | state =>
      simp only [entries, hr, regions, List.mem_cons] at member
      rcases member with rfl | rfl | member
      · refine ⟨fun h => absurd h xu, fun _ => ?_, fun h => absurd h xj⟩
        simp [roleVolume, hr]
      · refine ⟨fun h => absurd h dxu, fun _ => ?_, fun h => absurd h dxj⟩
        simp [roleVolume, hr]
      · have within := ih _ _ _ _ a member
        simpa [roleVolume, hr, Nat.add_assoc] using within
    | algebraic =>
      simp only [entries, hr, regions, List.mem_cons] at member
      rcases member with rfl | member
      · refine ⟨fun h => absurd h ju, fun h => ?_, fun _ => ?_⟩
        · rcases h with h | h
          · exact absurd h jx
          · exact absurd h jdx
        · simp [roleVolume, hr]
      · have within := ih _ _ _ _ a member
        simpa [roleVolume, hr, Nat.add_assoc] using within

/-- A region inside smaller blocks is inside larger ones. -/
theorem Region.Within.mono {r : Region} {inputs states outputs inputs' states' outputs' : Nat}
    (within : r.Within inputs states outputs) (hi : inputs ≤ inputs') (hs : states ≤ states')
    (ho : outputs ≤ outputs') : r.Within inputs' states' outputs' :=
  ⟨fun h => Nat.le_trans (within.1 h) hi, fun h => Nat.le_trans (within.2.1 h) hs,
    fun h => Nat.le_trans (within.2.2 h) ho⟩

/-- Every record region of an interface lies inside its block, whose extents are
the total volumes of the declared inputs, states and algebraic outputs. -/
theorem recordRegions_within (i : Interface) :
    ∀ a ∈ recordRegions i, a.2.Within (roleVolume .input i.declarations)
      (roleVolume .state i.declarations) (roleVolume .algebraic i.declarations) := by
  intro a member
  simpa using regions_within 0 0 0 1 i.declarations a member

end Rumoca.FMI3.Float64Table
