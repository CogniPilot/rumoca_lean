import RumocaEFMI.TensorContextIVP
import RumocaEFMI.TensorPublicStorage
import RumocaEFMI.TensorContextCalls

/-! The actual public RHS argument aliasing and retained declared storage.
This is a helper completion, not a whole DoStep execution claim. -/
noncomputable section
namespace Rumoca.EFMI.PublicRHS
open CMemory CMemory.TensorView CDeclaredMembers CDeclaredMembers.MemberStorage
open CTensor Solve.Tensor TensorProduction TensorPublicStorage TensorNumericalLinkage

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
      (show clockName ≠ squareVar.name by decide +kernel) 0
  · apply storage.status.framed
    simpa only [Address.index_zero] using member_preserved frame
      (show statusName ≠ squareVar.name by decide +kernel) 0

/-- On the actual ten-tree table and array-aware machine, the emitted RHS
returns the finite Solve result and preserves the SAME finite input/storage.
Header bindings, table lookup and output/input separation are derived. -/
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
          .pointer (some (base.member squareVar.name)), .integer inputVar.volume] heap finalHeap := by
  letI : CInterface := NumericalInterface.interface
  obtain ⟨finalHeap, reads, writes, frame, ran⟩ :=
    ContextIVP.derivative TensorArrayMembers.declarations objects unusedKernel heap (addresses base)
      input input result (by decide +kernel) storage.input_reads storage.input_reads storage.square
      (separate base) executed
  refine ⟨finalHeap, storage_after storage writes frame, reads, frame, ?_⟩
  simpa only [argument_values] using ran

end Rumoca.EFMI.PublicRHS
