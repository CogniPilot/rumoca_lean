import RumocaEFMI.TensorContextIVP
import RumocaEFMI.TensorPublicStorage
import RumocaEFMI.TensorContextCalls

/-! The actual public RHS argument aliasing and retained declared storage.
This is a helper completion, not a whole DoStep execution claim. -/
noncomputable section
namespace Rumoca.EFMI.PublicRHS
open CMemory CMemory.TensorView CDeclaredMembers CDeclaredMembers.MemberStorage
open CTensor Solve.Tensor TensorProduction TensorPublicStorage TensorNumericalLinkage
open CContextMachine TensorContextCalls

def addresses (base : Address) (name : String) : Address :=
  if name = "dx" then base.member squareVar.name else base.member inputVar.name

theorem argument_values (base : Address) :
    Lowering.Arguments.values (ProgramFixture.IVPEntry.plan inputShape).derivative.function.parameters
      (AddressedIVP.args (addresses base) inputShape) =
      [.pointer (some (base.member inputVar.name)), .pointer (some (base.member inputVar.name)),
        .pointer (some (base.member squareVar.name)), .integer inputVar.volume] := rfl

theorem separate (base : Address) :
    ∀ name, name = "x" ∨ name = "u" → ∀ i < inputShape.volume, ∀ j < inputShape.volume,
      (addresses base "dx").index i ≠ (addresses base name).index j := by
  intro name casesName i _ j _
  rcases casesName with rfl | rfl
  all_goals exact Address.fields_separate base squareVar.name inputVar.name (by decide +kernel) i j

/-- A numerical frame outside one whole member preserves every cell in a
distinct member. No assumed native struct offsets or duplicated cell list. -/
theorem member_preserved {before after : Heap} {base : Address} {output name : String}
    {count : Nat} (frame : ∀ q, (∀ i < count, q ≠ (base.member output).index i) →
    after q = before q) (different : name ≠ output) (j : Nat) :
    after ((base.member name).index j) = before ((base.member name).index j) :=
  frame _ (fun i _ => Address.fields_separate base name output different j i)

theorem storage_after (storage : Storage objects heap base input)
    (writes : Writable after (base.member squareVar.name) squareShape.volume)
    (frame : ∀ q, (∀ i < squareShape.volume, q ≠ (base.member squareVar.name).index i) →
      after q = heap q) : Storage objects after base input := by
  refine ⟨storage.object, ?_, writes, ?_, ?_, ?_⟩
  · exact storage.inputCells.framed (member_preserved frame (by decide +kernel))
  · exact writable_framed storage.jacobian (member_preserved frame (by decide +kernel))
  · apply storage.clock.framed
    simpa only [Address.index_zero] using member_preserved frame
      (show GALEC.Names.clock ≠ squareVar.name by decide +kernel) 0
  · apply storage.status.framed
    simpa only [Address.index_zero] using member_preserved frame
      (show statusName ≠ squareVar.name by decide +kernel) 0

/-- Reuse the actual numerical library in any enclosing table that preserves
its definitions; unrelated public methods need not agree. -/
theorem helper_in (p : CCalls.Program) (linked : CCalls.Typed.Extends definitions p)
    (objects : Objects) (heap : Heap) (base : Address) (input result : Values inputShape)
    (storage : Storage objects heap base input)
    (executed : Finite.Executes (ArrayProfile.squareProgram inputShape)
      (ArrayProfile.environment input input) result) :
    letI : CInterface := NumericalInterface.interface
    ∃ finalHeap, Storage objects finalHeap base input ∧
      Reads finalHeap (base.member squareVar.name) result ∧
      (∀ q, (∀ i < squareShape.volume, q ≠ (base.member squareVar.name).index i) →
        finalHeap q = heap q) ∧
      CallResult (expressions objects) p "rumoca_rhs"
        [.pointer (some (base.member inputVar.name)), .pointer (some (base.member inputVar.name)),
          .pointer (some (base.member squareVar.name)), .integer inputVar.volume] heap finalHeap := by
  letI : CInterface := NumericalInterface.interface
  obtain ⟨finalHeap, reads, writes, frame, ran⟩ :=
    AddressedIVP.derivative_call definitions (derivative_library_numerical inputShape)
      (derivative_defined inputShape) heap (PublicRHS.addresses base) input input result
      (by decide +kernel) storage.input_reads storage.input_reads storage.square
      (PublicRHS.separate base) executed
  refine ⟨finalHeap, PublicRHS.storage_after storage writes frame, reads, frame, ?_⟩
  have contextual := loop_call_result_context TensorArrayMembers.declarations objects p
    definitions linked TensorNumericalFieldFree.definition_body ((ran _).2 rfl)
  simpa only [PublicRHS.argument_values] using contextual

/-- The production table is an instance of the numerical extension theorem. -/
theorem helper (unusedKernel : CSyntax.Program) (objects : Objects) (heap : Heap)
    (base : Address) (input result : Values inputShape)
    (storage : Storage objects heap base input)
    (executed : Finite.Executes (ArrayProfile.squareProgram inputShape)
      (ArrayProfile.environment input input) result) :
    letI : CInterface := NumericalInterface.interface
    ∃ finalHeap, Storage objects finalHeap base input ∧
      Reads finalHeap (base.member squareVar.name) result ∧
      (∀ q, (∀ i < squareShape.volume, q ≠ (base.member squareVar.name).index i) →
        finalHeap q = heap q) ∧
      CContextMachine.CallResult (TensorContextCalls.expressions objects) (program unusedKernel)
        "rumoca_rhs"
        [.pointer (some (base.member inputVar.name)), .pointer (some (base.member inputVar.name)),
          .pointer (some (base.member squareVar.name)), .integer inputVar.volume] heap finalHeap :=
  helper_in (program unusedKernel) (numerical_in_actual unusedKernel)
    objects heap base input result storage executed

end Rumoca.EFMI.PublicRHS
