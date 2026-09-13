import RumocaC.StringCalls

/-! Construct a consistent selected string-library environment. The bindings
are the explicit C11 relations, not verified implementations of native libc.
Unrelated external routines can be supplied by callers of the execution proofs. -/
noncomputable section
namespace Rumoca.CStringCalls
open CMemory CCalls.Events
variable [interface : CInterface] {E : Type}

def routineNames : List String := ["strlen", "strspn", "strcmp"]

def library (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32) : String → Option (External E)
  | "strlen" => some (lengthExternal size)
  | "strspn" => some (spanExternal size)
  | "strcmp" => some (compareExternal integer)
  | _ => none

theorem library_name (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32) (name : String) (fn : External E)
    (found : library size integer name = some fn) :
    name ∈ routineNames ∧ fn.signature.name = name := by
  unfold library at found
  split at found
  all_goals first
    | cases Option.some.inj found
      exact ⟨by simp [routineNames], rfl⟩
    | cases found

/-- The selected routines cannot shadow an internal function. Construction
supplies the program's disjointness and name-coherence proofs. -/
def linked (internal : CCalls.Program)
    (fresh : ∀ name ∈ routineNames, internal.definitions name = none)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32)
    (addresses : Address → Option String) : Program E where
  internal := internal
  addresses := addresses
  externals := library size integer
  disjoint := fun name fn found => fresh name (library_name size integer name fn found).1
  names := fun name fn found => (library_name size integer name fn found).2

theorem linked_internal (internal : CCalls.Program)
    (fresh : ∀ name ∈ routineNames, internal.definitions name = none)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32)
    (addresses : Address → Option String) :
    (linked (E := E) internal fresh size integer addresses).internal = internal := rfl

end Rumoca.CStringCalls
