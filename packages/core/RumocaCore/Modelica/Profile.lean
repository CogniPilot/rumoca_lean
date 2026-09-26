import RumocaCore.Modelica.Unit
import RumocaCore.Modelica.Array
import RumocaCore.Modelica.Constant
import RumocaCore.Modelica.Annotation

/-! Profile selection over the general syntax tree. A meaning-changing
annotation is rejected first (`Annotation.screen`). At most one admitted
profile selects a tree (`select_disjoint`); every other tree the grammar accepts
is a static-semantic rejection. The rejection reported for a tree outside every
profile is the one that reads furthest into the source, since that profile's
shape matched the longest written prefix. -/
namespace Rumoca.Modelica.Profile
open _root_.Parser

inductive Selected where
  | unit (model : AST.Model)
  | square (model : ArrayProfile.Model)
  | rates (model : ConstantProfile.Model)

/-- The later of two rejections; the first on a tie. -/
def furthest (first second : Rejection) : Rejection :=
  if first.token < second.token then second else first

def select (d : Modelica.AST.StoredDefinition) : Except Rejection Selected := do
  Annotation.screen d
  match AST.select d, ArrayProfile.select d, ConstantProfile.select d with
  | .ok model, _, _ => .ok (.unit model)
  | _, .ok model, _ => .ok (.square model)
  | _, _, .ok model => .ok (.rates model)
  | .error unit, .error square, .error rates => .error (furthest (furthest unit square) rates)

private theorem square_third (m : ArrayProfile.Model) : m.tokens[2]? = some (.literal "input") := rfl
private theorem unit_third (m : AST.Model) : m.tokens[2]? = some (.ident "Real") := rfl
private theorem rates_third (m : ConstantProfile.Model) : m.tokens[2]? = some (.ident "Real") := rfl

private theorem rates_length (m : ConstantProfile.Model) : 16 < m.tokens.length := by
  simp [ConstantProfile.Model.tokens, ConstantProfile.Model.states, ConstantProfile.Model.equations,
    ConstantProfile.declTokens, ConstantProfile.equationTokens]
  omega

/-- No tree selects two profiles. -/
theorem select_disjoint (d : Modelica.AST.StoredDefinition) :
    (∀ u s, AST.select d = .ok u → ArrayProfile.select d = .ok s → False) ∧
    (∀ u r, AST.select d = .ok u → ConstantProfile.select d = .ok r → False) ∧
    (∀ s r, ArrayProfile.select d = .ok s → ConstantProfile.select d = .ok r → False) := by
  refine ⟨fun u s hu hs => ?_, fun u r hu hr => ?_, fun s r hs hr => ?_⟩
  · have same := (AST.select_printed hu).symm.trans (ArrayProfile.select_printed hs)
    have third := congrArg (·[2]?) same
    simp only [unit_third, square_third] at third
    cases third
  · have same := (AST.select_printed hu).symm.trans (ConstantProfile.select_printed hr)
    have length := congrArg List.length same
    have bound := rates_length r
    simp only [AST.Model.tokens, List.length_cons, List.length_nil] at length
    omega
  · have same := (ArrayProfile.select_printed hs).symm.trans (ConstantProfile.select_printed hr)
    have third := congrArg (·[2]?) same
    simp only [rates_third, square_third] at third
    cases third

/-! ### Annotations -/

private theorem unit_unannotated {d : Modelica.AST.StoredDefinition} {m : AST.Model}
    (h : AST.select d = .ok m) : Annotation.Unannotated (Print.storedDefinition d) := by
  rw [AST.select_printed h]
  simp [Annotation.Unannotated, AST.Model.tokens]

private theorem square_unannotated {d : Modelica.AST.StoredDefinition} {m : ArrayProfile.Model}
    (h : ArrayProfile.select d = .ok m) : Annotation.Unannotated (Print.storedDefinition d) := by
  rw [ArrayProfile.select_printed h]
  obtain ⟨⟨_, _, _, _, _⟩, ⟨_, _, ⟨_, _⟩, _, ⟨_, ⟨_, _⟩, _⟩⟩, _⟩ := m
  simp [Annotation.Unannotated, ArrayProfile.Model.tokens, ArrayProfile.Header.tokens,
    ArrayProfile.Body.tokens, ArrayProfile.Product.tokens, ArrayProfile.Call.tokens]

private theorem rates_unannotated {d : Modelica.AST.StoredDefinition} {m : ConstantProfile.Model}
    (h : ConstantProfile.select d = .ok m) : Annotation.Unannotated (Print.storedDefinition d) := by
  rw [ConstantProfile.select_printed h]
  exact fun member => (m.tokens_plain _ member).2 rfl

/-- A selected tree has no annotation clause. -/
theorem selected_unannotated {d : Modelica.AST.StoredDefinition} {s : Selected}
    (h : select d = .ok s) : Annotation.Unannotated (Print.storedDefinition d) := by
  unfold select at h
  cases screened : Annotation.screen d with
  | error _ => rw [screened] at h; cases h
  | ok _ =>
    rw [screened] at h
    simp only [bind, Except.bind] at h
    split at h
    · exact unit_unannotated (by assumption)
    · exact square_unannotated (by assumption)
    · exact rates_unannotated (by assumption)
    · cases h

/-- Annotations do not affect selection: discarding every annotation clause of
a selected tree selects the same record. -/
theorem annotation_irrelevant {d : Modelica.AST.StoredDefinition} {s : Selected}
    (h : select d = .ok s) : select (Annotation.erase d) = .ok s := by
  rw [Annotation.erase_unannotated (selected_unannotated h)]
  exact h

/-- A tree `select` rejects is the tree of no selected parse of any profile. -/
theorem rejected {source : String} {r : Rejection} (tree : Modelica.Parsed source)
    (rejection : select tree.ast = .error r) :
    (AST.selection.Parsed source → False) ∧ (ArrayProfile.selection.Parsed source → False) ∧
      (ConstantProfile.selection.Parsed source → False) := by
  have unit : ∀ m, AST.select tree.ast ≠ .ok m := fun m h => by
    have screened := Annotation.screen_unannotated (unit_unannotated h)
    simp [select, screened, h, bind, Except.bind] at rejection
  have square : ∀ m, ArrayProfile.select tree.ast ≠ .ok m := fun m h => by
    have screened := Annotation.screen_unannotated (square_unannotated h)
    simp only [select, screened, bind, Except.bind] at rejection
    split at rejection <;> simp_all
  have rates : ∀ m, ConstantProfile.select tree.ast ≠ .ok m := fun m h => by
    have screened := Annotation.screen_unannotated (rates_unannotated h)
    simp only [select, screened, bind, Except.bind] at rejection
    split at rejection <;> simp_all
  refine ⟨fun p => unit p.ast ?_, fun p => square p.ast ?_, fun p => rates p.ast ?_⟩ <;>
    rw [← Modelica.Parsed.unique p.tree tree] <;> exact p.selected

end Rumoca.Modelica.Profile
