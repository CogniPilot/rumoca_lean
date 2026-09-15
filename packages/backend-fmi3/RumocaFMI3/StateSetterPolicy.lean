import RumocaFMI3.Float64SetMetadata
import RumocaCore.FMI3.Lifecycle

/-! State-specific permissions for the admitted scalar profile. Reviewed against FMI 3.0.2 and merged clarification #1956; generic local-variable wording remains an explicitly recorded editorial conflict. -/
namespace Rumoca.FMI3.StateSetterPolicy
open XML Float64Metadata

/-- Resolve a continuous state by its derivative relationship in ModelStructure.
Initialization and reinitialization attributes are checked separately. -/
def StateDeclaration (root : Element) (reference : Nat) (declaration : Element) : Prop :=
  ∃ modelVariables layout entry derivative derivativeReference,
    root.children.filter (fun node => node.name == "ModelVariables") = [modelVariables] ∧
    root.children.filter (fun node => node.name == "ModelStructure") = [layout] ∧
    entry ∈ layout.children.filter (fun node => node.name == "ContinuousStateDerivative") ∧
    referenceOf entry = some derivativeReference ∧
    modelVariables.children.filter (fun node => referenceOf node == some derivativeReference) = [derivative] ∧
    StateMetadata.ScalarContinuous derivative ∧
    (derivative.attributes.lookup "derivative").bind decimal = some reference ∧
    modelVariables.children.filter (fun node => referenceOf node == some reference) = [declaration] ∧
    declaration.name = "Float64" ∧
    declaration.attributes.lookup "variability" = some "continuous" ∧
    declaration.children.filter (fun node => node.name == "Dimension") = []

/-- Only for a previously identified continuous-state declaration. FMI
Instantiated permits exact/approx initial values; Initialization requires exact;
ME Event additionally requires no reinitialization, while Continuous-Time
permits states independently of their causality and initial attributes.
CS Event Mode is not enabled in this profile. -/
def PhasePermission (kind : Kind) (mode : Mode) (declaration : Element) : Prop :=
  match mode with
  | .instantiated => declaration.attributes.lookup "variability" ≠ some "constant" ∧
      (declaration.attributes.lookup "initial" = some "exact" ∨
       declaration.attributes.lookup "initial" = some "approx")
  | .initialization => declaration.attributes.lookup "variability" ≠ some "constant" ∧
      declaration.attributes.lookup "initial" = some "exact"
  | .event => kind = .me ∧ Float64SetMetadata.NoReinit declaration
  | .continuous => kind = .me
  | .step | .terminated => False

def Permitted (root : Element) (reference : Nat) (kind : Kind) (mode : Mode) : Prop :=
  ∃ declaration, StateDeclaration root reference declaration ∧ PhasePermission kind mode declaration

theorem StateDeclaration.unique (first : StateDeclaration root reference declaration)
    (second : StateDeclaration root reference other) : declaration = other := by
  obtain ⟨vars, _, _, _, _, hv, _, _, _, _, _, _, selected, _⟩ := first
  obtain ⟨vars', _, _, _, _, hv', _, _, _, _, _, _, selected', _⟩ := second
  have sameVars := List.singleton_inj.mp (hv.symm.trans hv')
  cases sameVars
  exact List.singleton_inj.mp (selected.symm.trans selected')

theorem writable_declaration (writable : Float64SetMetadata.Writable root reference variableName) :
    ∃ declaration, StateDeclaration root reference declaration ∧
      declaration.attributes.lookup "name" = some variableName ∧
      declaration.attributes.lookup "causality" = some "local" ∧
      declaration.attributes.lookup "initial" = some "exact" ∧
      Float64SetMetadata.NoReinit declaration := by
  obtain ⟨vars, layout, entry, derivative, declaration, dref,
    hv, hl, member, er, dfound, dtyped, follows, selected, dtype, named, continuous, scalar, locality, initial, reinit⟩ := writable
  exact ⟨declaration, ⟨vars, layout, entry, derivative, dref,
    hv, hl, member, er, dfound, dtyped, follows, selected, dtype, continuous, scalar⟩,
    named, locality, initial, reinit⟩

/-- The existing mode guard is exact for every XML state with the accepted
initialization profile, rather than only for one emitted variable spelling. -/
theorem writable_modes (writable : Float64SetMetadata.Writable root reference variableName)
    (kind : Kind) (mode : Mode) :
    Permitted root reference kind mode ↔ Reference.Allowed .setStart kind mode := by
  obtain ⟨declaration, selected, named, locality, initial, reinit⟩ := writable_declaration writable
  have continuous : declaration.attributes.lookup "variability" = some "continuous" := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hc, _⟩ := selected
    exact hc
  have reduce : Permitted root reference kind mode ↔ PhasePermission kind mode declaration := by
    constructor
    · rintro ⟨other, selected', permitted⟩
      have same := selected.unique selected'
      cases same
      exact permitted
    · intro permitted
      exact ⟨declaration, selected, permitted⟩
  rw [reduce]
  cases kind <;> cases mode <;>
    simp [PhasePermission, Reference.Allowed, continuous, initial, reinit]

theorem writable_guard (writable : Float64SetMetadata.Writable root reference variableName)
    (kind : Kind) (mode : Mode) :
    allowed .setStart kind mode = true ↔ Permitted root reference kind mode :=
  (allowed_correct .setStart kind mode).trans (writable_modes writable kind mode).symm

/-- ME state selection in Continuous-Time Mode depends on state identity,
not on local/output causality or exact/calculated initialization metadata. -/
theorem continuous_state (selected : StateDeclaration root reference declaration) :
    Permitted root reference .me .continuous := ⟨declaration, selected, rfl⟩

theorem event_state (selected : StateDeclaration root reference declaration)
    (reinit : Float64SetMetadata.NoReinit declaration) :
    Permitted root reference .me .event := ⟨declaration, selected, rfl, reinit⟩

theorem cs_state_simulation (mode : Mode) (later : mode = .step ∨ mode = .event ∨ mode = .continuous) :
    ¬ Permitted root reference .cs mode := by
  rintro ⟨declaration, selected, permitted⟩
  rcases later with rfl | rfl | rfl <;> simp [PhasePermission] at permitted

/-- The independently parsed actual XML contract supplies the same state
selection for every interface and mode. It imposes no new artifact premise. -/
theorem artifact_modes (contract : Float64SetMetadata.Contract source text) :
    ∃ root, XML.Document root text ∧ Float64SetMetadata.Writable root 1 source.state ∧
      ∀ kind mode, allowed .setStart kind mode = true ↔ Permitted root 1 kind mode := by
  obtain ⟨root, document, writable, _⟩ := contract
  exact ⟨root, document, writable, writable_guard writable⟩

end Rumoca.FMI3.StateSetterPolicy
