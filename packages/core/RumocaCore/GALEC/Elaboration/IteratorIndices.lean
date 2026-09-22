import RumocaCore.GALEC.Elaboration.IteratorNames
import GALECParser.AST

/-! Iterator-reference indices, a reusable branch of static Integer elaboration.
Only ordinary unindexed local identifiers (optionally parenthesized) denote an
iterator. Neither raw numeric tokens, state paths nor indexed locals are names.
No production admission or general Integer-expression completeness is claimed. -/
namespace Rumoca.GALEC.Elaboration.IteratorIndices
open _root_.Parser

inductive Surface : AST.Expr → String → Prop where
  | reference (name : String) :
      Surface (.reference (AST.Reference.unindexed (.ident name) [])) name
  | parens : Surface body name → Surface (.parens body) name

def read : AST.Expr → Option String
  | .reference ⟨⟨.ident name, []⟩, []⟩ => some name
  | .parens body => read body
  | _ => none

theorem read_sound (expr : AST.Expr) (name : String) (found : read expr = some name) :
    Surface expr name := by
  unfold read at found
  split at found
  · rename_i actual
    cases Option.some.inj found
    exact .reference _
  · rename_i body
    exact .parens (read_sound body name found)
  · contradiction
termination_by sizeOf expr

theorem read_complete (spelling : Surface expr name) : read expr = some name := by
  induction spelling with
  | reference name => rfl
  | parens inner ih => exact ih

theorem read_iff (expr : AST.Expr) (name : String) :
    read expr = some name ↔ Surface expr name :=
  ⟨read_sound expr name, read_complete⟩

def elaborate (names : IteratorNames bounds) (extent : Nat) (expr : AST.Expr) :
    Option (IndexTerm bounds extent) :=
  (read expr).bind fun name => (names.lookupAt name extent).map IndexTerm.iterator

/-- A syntax-directed typing/lowering judgment, independent of `elaborate`. -/
inductive Elaborates (names : IteratorNames bounds) (extent : Nat) :
    AST.Expr → IndexTerm bounds extent → Prop where
  | iterator (spelling : Surface expr name)
      (binding : IteratorNames.Resolves names name ⟨extent, ref⟩) :
      Elaborates names extent expr (.iterator ref)

theorem elaborate_iff (names : IteratorNames bounds) (extent : Nat) (expr : AST.Expr)
    (term : IndexTerm bounds extent) :
    elaborate names extent expr = some term ↔ Elaborates names extent expr term := by
  simp only [elaborate, Option.bind_eq_some_iff, Option.map_eq_some_iff]
  constructor
  · rintro ⟨name, named, ref, bound, equal⟩
    cases equal
    exact .iterator ((read_iff expr name).mp named)
      ((IteratorNames.lookupAt_iff names name extent ref).mp bound)
  · intro typed
    cases typed with
    | @iterator name ref spelling binding =>
      exact ⟨name, read_complete spelling, ref,
        (IteratorNames.lookupAt_iff names name extent ref).mpr binding, rfl⟩

/-- Mathematical source Integer evaluation; it does not mention the lowered
index term, elaborator, Fin decoder, or executable name lookup. -/
inductive Evaluates (names : IteratorNames bounds) (env : IteratorEnv bounds) :
    AST.Expr → Int → Prop where
  | iterator (spelling : Surface expr name)
      (binding : IteratorNames.Resolves names name ⟨bound, ref⟩) :
      Evaluates names env expr (Int.ofNat (env ref).val + 1)

variable {bounds : List Nat} {names : IteratorNames bounds} {extent : Nat}
  {expr : AST.Expr} {term : IndexTerm bounds extent} {env : IteratorEnv bounds} {a b : Int}

theorem lowering_sound (typed : Elaborates names extent expr term)
    (env : IteratorEnv bounds) :
    Evaluates names env expr (Int.ofNat (term.eval env).val + 1) := by
  cases typed with
  | iterator spelling binding => exact .iterator spelling binding

theorem evaluates_unique (first : Evaluates names env expr a)
    (second : Evaluates names env expr b) : a = b := by
  cases first with
  | @iterator name bound ref spelling binding =>
    cases second with
    | @iterator otherName otherBound otherRef otherSpelling otherBinding =>
      have sameName := Option.some.inj
        ((read_complete spelling).symm.trans (read_complete otherSpelling))
      subst otherName
      have sameEntry := Option.some.inj
        (((IteratorNames.lookup_iff names name ⟨bound, ref⟩).mpr binding).symm.trans
          ((IteratorNames.lookup_iff names name ⟨otherBound, otherRef⟩).mpr otherBinding))
      cases sameEntry
      rfl

/-- Exact value correspondence, not merely an in-bounds approximation. -/
theorem lowering_correct (typed : Elaborates names extent expr term)
    (env : IteratorEnv bounds) (value : Int) :
    Evaluates names env expr value ↔ value = Int.ofNat (term.eval env).val + 1 := by
  constructor
  · intro evaluated
    exact evaluates_unique evaluated (lowering_sound typed env)
  · rintro rfl
    exact lowering_sound typed env

end Rumoca.GALEC.Elaboration.IteratorIndices
