import RumocaC.ObjectDeclaration
import RumocaC.ObjectStorage

/-! Connect structured C record/array declarations to object-level storage.
Type names have explicit meanings supplied by the surrounding translation unit.
The record interpreter resolves only already-defined field types; it cannot
invent a type for an unknown spelling or introduce recursive by-value records.
Native layout, header meanings and C constant representability remain separate.
-/
namespace Rumoca.CObject
open CMemory

abbrev Types := String → Option Shape

def resolveFields (types : Types) : List Field → Option (List (String × Shape))
  | [] => some []
  | field :: rest => do
    let type ← types field.type
    return (field.name, type) :: (← resolveFields types rest)

def Record.resolve (types : Types) (record : Record) : Option Shape :=
  Shape.record <$> resolveFields types record.fields

inductive FieldsMean (types : Types) : List Field → List (String × Shape) → Prop where
  | nil : FieldsMean types [] []
  | cons : types field.type = some type → FieldsMean types rest fields →
      FieldsMean types (field :: rest) ((field.name, type) :: fields)

theorem resolveFields_iff : resolveFields types fields = some meanings ↔ FieldsMean types fields meanings := by
  constructor
  · intro resolved
    induction fields generalizing meanings with
    | nil => simp [resolveFields] at resolved; subst meanings; exact .nil
    | cons field rest ih =>
        simp only [resolveFields, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq] at resolved
        obtain ⟨type, typed, tail, resolved, rfl⟩ := resolved
        exact .cons typed (ih resolved)
  · intro meaning
    induction meaning with
    | nil => rfl
    | cons typed _ ih => simp [resolveFields, typed, ih]

theorem record_resolves (record : Record) (types : Types) (shape : Shape) : record.resolve types = some shape ↔
    ∃ fields, FieldsMean types record.fields fields ∧ shape = .record fields := by
  simp only [Record.resolve, Functor.map, Option.map_eq_some_iff, resolveFields_iff]
  constructor
  · rintro ⟨fields, resolved, rfl⟩; exact ⟨fields, resolved, rfl⟩
  · rintro ⟨fields, resolved, rfl⟩; exact ⟨fields, resolved, rfl⟩

/-- A record's field order and every declared name are retained by resolution. -/
theorem FieldsMean.names (meaning : FieldsMean types fields meanings) :
    meanings.map Prod.fst = fields.map Field.name := by
  induction meaning with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- Exact initialization of the admitted array object and preservation of every
other cell. This judgment is the static-duration object semantics, not a runtime
allocator or a native layout assumption. -/
def ArrayInitializes (types : Types) (array : StaticArray) (block : Nat) (before after : Heap) : Prop :=
  ∃ shape, types array.type = some shape ∧
    (∀ p type, cellType shape block array.count p = some type → before p = none) ∧
    (∀ p type, cellType shape block array.count p = some type → after p = some (zeroCell type)) ∧
    (∀ p, cellType shape block array.count p = none → after p = before p)

theorem array_initializes (typed : types array.type = some shape)
    (fresh : ∀ p type, cellType shape block array.count p = some type → before p = none) :
    ArrayInitializes types array block before (initial before shape block array.count) :=
  ⟨shape, typed, fresh, fun _ _ found => initial_at found, fun _ outside => initial_frame outside⟩

/-- One declaration supplies both the independently denoted C text and the
static object initialization contract, retaining the same type and bound. -/
theorem array_printed_initializes (printable : ArrayPrintable typedefs array)
    (typed : types array.type = some shape)
    (fresh : ∀ p type, cellType shape block array.count p = some type → before p = none) :
    Renders (ArrayPhrase typedefs) StaticArray.render array ∧
    ArrayInitializes types array block before (initial before shape block array.count) ∧
    CReadOnly.Preserves before (initial before shape block array.count) :=
  ⟨array_renders printable, array_initializes typed fresh, initial_readonly fresh⟩

end Rumoca.CObject
