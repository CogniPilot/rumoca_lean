import RumocaCore.GALEC.Elaboration.Capabilities.DoStep.Policy
import RumocaCore.GALEC.Elaboration.Bodies.Lowering

/-! Independent recursive write-side policy over original AST statements.
It says nothing about evaluation success, ranges, exceptional outcomes or
complete method legality. Every branch body obeys it; error-signal statements
write no storage. Only the actually selected DoStep may use this policy. -/
namespace Rumoca.GALEC.Elaboration.Capabilities.DoStep
open Rumoca.Tensor

mutual
inductive StatementWrites (declarations : List Declarations.Real.Descriptor) : AST.Statement → Prop where
  | assign (allowed : ∃ declaration ∈ declarations, ∃ indices,
      Path.Surface target [declaration.name] indices ∧ Writable declaration) :
      StatementWrites declarations (.assign target value)
  | branch : BranchesWrites declarations branches otherwise →
      StatementWrites declarations (.ifThen branches otherwise)
  | loop : BodyWrites declarations body →
      StatementWrites declarations (.forLoop binder start stride stop body)
  | signal : StatementWrites declarations (.signal raised)

/-- Every branch body and the `else` body obey the write policy. -/
inductive BranchesWrites (declarations : List Declarations.Real.Descriptor) :
    List (AST.Condition × List AST.Statement) → Option (List AST.Statement) → Prop where
  | none : BranchesWrites declarations [] none
  | otherwise : BodyWrites declarations body → BranchesWrites declarations [] (some body)
  | cons : BodyWrites declarations body → BranchesWrites declarations rest otherwise →
      BranchesWrites declarations ((test, body) :: rest) otherwise

inductive BodyWrites (declarations : List Declarations.Real.Descriptor) : List AST.Statement → Prop where
  | nil : BodyWrites declarations []
  | cons : StatementWrites declarations source → BodyWrites declarations rest →
      BodyWrites declarations (source :: rest)
end

mutual
theorem statement_writes
    (typed : Bodies.StatementElaborates (Layout.bindings (fields declarations))
      HasShape ceiling names source stmt) : StatementWrites declarations source := by
  cases typed with
  | assign assignment =>
    cases assignment with
    | assign target value =>
      obtain ⟨declaration, present, indices, spelling, _, writable⟩ := target_writable target
      exact .assign ⟨declaration, present, indices, spelling, writable⟩
  | branch chosen => exact .branch (branches_writes chosen)
  | loop _ body => exact .loop (body_writes body)
  | signal _ => exact .signal
termination_by sizeOf source

theorem branches_writes
    (typed : Bodies.BranchesElaborates (Layout.bindings (fields declarations))
      HasShape ceiling names sources otherwise stmt) :
    BranchesWrites declarations sources otherwise := by
  cases typed with
  | none => exact .none
  | otherwise body => exact .otherwise (body_writes body)
  | cons _ body rest => exact .cons (body_writes body) (branches_writes rest)
termination_by sizeOf sources + sizeOf otherwise

theorem body_writes
    (typed : Bodies.BodyElaborates (Layout.bindings (fields declarations))
      HasShape ceiling names sources stmt) : BodyWrites declarations sources := by
  cases typed with
  | nil => exact .nil
  | cons first rest => exact .cons (statement_writes first) (body_writes rest)
termination_by sizeOf sources
end

theorem lowered_body_writes
    (lowered : Bodies.statements (Layout.bindings (fields declarations)) lookupShape ceiling names sources = some stmt) :
    BodyWrites declarations sources :=
  body_writes (Bodies.statements_sound _ lookupShape (fun key shape => lookupShape key = some shape)
    (fun _ _ => Iff.rfl) ceiling names sources stmt lowered)

end Rumoca.GALEC.Elaboration.Capabilities.DoStep
