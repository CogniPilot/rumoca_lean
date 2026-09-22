import GALECParser.AST

/-! Core state-path classification on the actual AST. Qualified names remain
lists, never dotted strings. Final-component indices are retained verbatim;
indexed intermediate components need a future record/array elaboration rule
and are rejected here, not erased or flattened. This is not name resolution. -/
namespace Rumoca.GALEC.Elaboration.Path
open _root_.Parser

inductive Components : List AST.Component → List String → List AST.Expr → Prop where
  | leaf (name : String) (indices : List AST.Expr) :
      Components [⟨.ident name, indices⟩] [name] indices
  | step (name : String) : Components tail path indices →
      Components (⟨.ident name, []⟩ :: tail) (name :: path) indices

def readComponents : List AST.Component → Option (List String × List AST.Expr)
  | [⟨.ident name, indices⟩] => some ([name], indices)
  | ⟨.ident name, []⟩ :: next :: tail =>
      (readComponents (next :: tail)).map fun (path, indices) => (name :: path, indices)
  | _ => none

theorem components_sound (parts : List AST.Component) (path : List String)
    (indices : List AST.Expr) (found : readComponents parts = some (path, indices)) :
    Components parts path indices := by
  unfold readComponents at found
  split at found
  · cases Option.some.inj found
    exact .leaf _ _
  · rename_i name next tail
    simp only [Option.map_eq_some_iff] at found
    obtain ⟨⟨key, subscripts⟩, rest, same⟩ := found
    cases same
    exact .step name (components_sound (next :: tail) key subscripts rest)
  · contradiction
termination_by parts.length

theorem components_complete (spelling : Components parts path indices) :
    readComponents parts = some (path, indices) := by
  induction spelling with
  | leaf name indices => rfl
  | @step tail path indices name rest ih =>
    cases tail with
    | nil => cases rest
    | cons first remaining =>
      change (readComponents (first :: remaining)).map
        (fun (key, subscripts) => (name :: key, subscripts)) = some (name :: path, indices)
      rw [ih]
      rfl

theorem components_iff (parts : List AST.Component) (path : List String)
    (indices : List AST.Expr) :
    readComponents parts = some (path, indices) ↔ Components parts path indices :=
  ⟨components_sound parts path indices, components_complete⟩

theorem key_nonempty (spelling : Components parts path indices) : path ≠ [] := by
  cases spelling <;> simp

inductive Surface : AST.Reference → List String → List AST.Expr → Prop where
  | self : Components fields path indices →
      Surface ⟨⟨.literal "self", []⟩, fields⟩ path indices

def read : AST.Reference → Option (List String × List AST.Expr)
  | ⟨⟨.literal "self", []⟩, fields⟩ => readComponents fields
  | _ => none

theorem read_sound (ref : AST.Reference) (path : List String) (indices : List AST.Expr)
    (found : read ref = some (path, indices)) : Surface ref path indices := by
  unfold read at found
  split at found
  · exact .self (components_sound _ _ _ found)
  · contradiction

theorem read_complete (spelling : Surface ref path indices) :
    read ref = some (path, indices) := by
  cases spelling with
  | self components => exact components_complete components

theorem read_iff (ref : AST.Reference) (path : List String) (indices : List AST.Expr) :
    read ref = some (path, indices) ↔ Surface ref path indices :=
  ⟨read_sound ref path indices, read_complete⟩

end Rumoca.GALEC.Elaboration.Path
