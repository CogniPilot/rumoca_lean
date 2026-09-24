import RumocaCore.GALEC.Elaboration.Static.Naturals

/-! Positive static declaration extents. Each written extent is a static
Integer expression (eFMI G-2 constant dimensions) evaluated under an empty
shape lookup, so an extent never depends on another declaration's size. This
traverses only the written axes, retaining their order and rank; it never
enumerates tensor cells. The caller supplies a mathematical Nat ceiling, not
an implicit machine width. Empty extents represent scalar rank here. -/
namespace Rumoca.GALEC.Elaboration.Declarations.Extents
open _root_.Parser Rumoca.Tensor

/-- No shape is known while declaration extents are elaborated. -/
def noShape : List String → Option Shape := fun _ => none

def Unknown (_ : List String) (_ : Shape) : Prop := False

theorem noShape_iff (key : List String) (shape : Shape) : noShape key = some shape ↔ Unknown key shape := by
  simp [noShape, Unknown]

/-- Independent meaning of one extent: its static value, positive and bounded. -/
inductive AxisDenotes (ceiling : Nat) : AST.Expr → Nat → Prop where
  | static (evaluated : Static.Naturals.Evaluates Unknown source extent)
      (positive : 0 < extent) (bounded : extent ≤ ceiling) :
      AxisDenotes ceiling source extent

/-- Independent ordered list meaning, including the rank-zero case. -/
inductive Denotes (ceiling : Nat) : List AST.Expr → List Nat → Prop where
  | nil : Denotes ceiling [] []
  | cons : AxisDenotes ceiling source extent → Denotes ceiling sources dims →
      Denotes ceiling (source :: sources) (extent :: dims)

def readAxis (ceiling : Nat) (source : AST.Expr) : Option Nat :=
  (Static.Naturals.read noShape source).bind fun extent =>
    if 0 < extent ∧ extent ≤ ceiling then some extent else none

def read (ceiling : Nat) : List AST.Expr → Option (List Nat)
  | [] => some []
  | source :: sources => (readAxis ceiling source).bind fun extent =>
      (read ceiling sources).map (extent :: ·)

theorem readAxis_iff (ceiling : Nat) (source : AST.Expr) (extent : Nat) :
    readAxis ceiling source = some extent ↔ AxisDenotes ceiling source extent := by
  constructor
  · intro found
    obtain ⟨candidate, evaluated, fitted⟩ := Option.bind_eq_some_iff.mp found
    split at fitted
    · rename_i bounds
      cases Option.some.inj fitted
      exact .static ((Static.Naturals.read_iff _ _ noShape_iff _ _).mp evaluated) bounds.1 bounds.2
    · contradiction
  · intro denoted
    cases denoted with
    | static evaluated positive bounded =>
      simp only [readAxis, (Static.Naturals.read_iff _ _ noShape_iff _ _).mpr evaluated,
        Option.bind_some, if_pos (And.intro positive bounded)]

theorem read_iff (ceiling : Nat) (sources : List AST.Expr) (dims : List Nat) :
    read ceiling sources = some dims ↔ Denotes ceiling sources dims := by
  induction sources generalizing dims with
  | nil =>
    constructor
    · intro found
      cases Option.some.inj found
      exact .nil
    · intro denoted
      cases denoted
      rfl
  | cons source sources ih =>
    constructor
    · intro found
      obtain ⟨extent, head, tail⟩ := Option.bind_eq_some_iff.mp found
      obtain ⟨rest, lowered, same⟩ := Option.map_eq_some_iff.mp tail
      cases same
      exact .cons ((readAxis_iff _ _ _).mp head) ((ih _).mp lowered)
    · intro denoted
      cases denoted with
      | cons head tail =>
        simp only [read, (readAxis_iff _ _ _).mpr head, Option.bind_some,
          (ih _).mpr tail, Option.map_some]

/-- The canonical numeral of every positive bounded extent denotes it. -/
theorem natural_denotes (positive : 0 < extent) (bounded : extent ≤ ceiling) :
    AxisDenotes ceiling (.literal (.number (toString extent))) extent :=
  .static (.literal rfl) positive bounded

theorem rank_preserved (denoted : Denotes ceiling sources dims) :
    dims.length = sources.length := by
  induction denoted with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem axis_bounds (denoted : AxisDenotes ceiling source extent) :
    0 < extent ∧ extent ≤ ceiling := by
  cases denoted with
  | static _ positive bounded => exact ⟨positive, bounded⟩

theorem bounds (denoted : Denotes ceiling sources dims) :
    ∀ extent ∈ dims, 0 < extent ∧ extent ≤ ceiling := by
  induction denoted with
  | nil => simp
  | cons head _ ih =>
    intro extent member
    cases List.mem_cons.mp member with
    | inl same => subst extent; exact axis_bounds head
    | inr tail => exact ih extent tail

end Rumoca.GALEC.Elaboration.Declarations.Extents
