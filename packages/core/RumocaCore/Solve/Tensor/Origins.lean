import RumocaCore.Solve.Tensor
import Parser.ProvenanceExtension

/-! Required occurrence metadata for tensor programs. The pure programs remain
usable as semantic values; deployment roots must supply a complete indexed
trace. Operand occurrences are distinct from the register definitions they read. -/
namespace Rumoca.Solve.Tensor
open _root_.Parser.Provenance (Table Node)

variable {Site Rule : Type} {table before after : Table Site Rule}
abbrev Origin (table : Table Site Rule) := _root_.Parser.Provenance.Ref table

inductive Program.Origins (table : Table Site Rule) : Program Γ shape → Type where
  | ret (operation reference : Origin table) : Origins table (.ret register)
  | fill {program : Program (shape :: Γ) result}
      (operation : Origin table) (next : Origins table program) :
      Origins table (.fill shape literal program)
  | binary {lhs rhs : Ref Γ shape} {program : Program (shape :: Γ) result}
      (operation left right : Origin table) (next : Origins table program) :
      Origins table (.binary op lhs rhs program)

def Program.Origins.root : Program.Origins table program → Origin table
  | .ret operation _ => operation
  | .fill operation _ => operation
  | .binary operation _ _ _ => operation

def Program.Origins.extend (extension : before.Extension after) :
    Program.Origins before program → Program.Origins after program
  | .ret operation reference => .ret (extension.ref operation) (extension.ref reference)
  | .fill operation next => .fill (extension.ref operation) (next.extend extension)
  | .binary operation left right next =>
      .binary (extension.ref operation) (extension.ref left) (extension.ref right)
        (next.extend extension)

def Program.Origins.Every (check : Node Site Rule → Prop) :
    Program.Origins table program → Prop
  | .ret operation reference => check (table.get operation) ∧ check (table.get reference)
  | .fill operation next => check (table.get operation) ∧ next.Every check
  | .binary operation left right next =>
      check (table.get operation) ∧ check (table.get left) ∧
        check (table.get right) ∧ next.Every check

theorem Program.Origins.extend_every (extension : before.Extension after)
    (check : Node Site Rule → Prop) (origins : Program.Origins before program) :
    (origins.extend extension).Every check ↔ origins.Every check := by
  induction origins with
  | ret operation reference => simp only [extend, Every, extension.lookup]
  | fill operation next ih => simp only [extend, Every, extension.lookup, ih]
  | binary operation left right next ih => simp only [extend, Every, extension.lookup, ih]

theorem Program.Origins.extend_root (extension : before.Extension after)
    (origins : Program.Origins before program) :
    (origins.extend extension).root = extension.ref origins.root := by
  cases origins <;> rfl

end Rumoca.Solve.Tensor
