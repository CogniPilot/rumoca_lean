import RumocaFMI3.MEControlEnvironment
import RumocaFMI3.EventEntryContract
import RumocaFMI3.CompletedContract
import RumocaFMI3.DiscreteContract
import RumocaFMI3.TimeContract

/-! Control contracts prepared from the actual table and read-only literal
pool, for arbitrary later heaps preserving that pool. Existing literal
preparation supplies the diagnostics; the shared runtime bridge supplies
complete calls, including every represented failure and callback outcome. -/
noncomputable section
namespace Rumoca.FMI3.MEControlEnvironment.EntryControl
open CTree CMemory CBody CLiteral CCalls.Events StaticFactory
open EventEntry

structure PreparedContract (model : Solve.FMI3Model source) (entry : EventEntry.Entry) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)) : Prop where
  quiet : ∀ (header : CFenv.Header) (E : Type) (objects : Objects) (firstBlock : Nat),
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : CCalls.Events.Program E),
      program.internal = LiteralPreparation.program model sigs → QuietContract entry program
  failures : ∀ (header : CFenv.Header) (before : Heap) (firstBlock : Nat) (signed : Bool) (objects : Objects)
    (heap : Heap), CReadOnly.Preserves (pool.install before firstBlock signed) heap →
    ∃ category message,
      pool.addresses firstBlock "logStatus" = some category ∧
      pool.addresses firstBlock ErrorCalls.rejectionMessage = some message ∧
      Stored signed heap category "logStatus" ∧ Stored signed heap message ErrorCalls.rejectionMessage ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (E : Type) (program : CCalls.Events.Program E),
         program.internal = LiteralPreparation.program model sigs → SuppressedContract entry program heap) ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (program : CCalls.Events.Program Invocation),
         program.internal = LiteralPreparation.program model sigs → LoggedContract entry program category message heap signed)

theorem prepared_correct (model : Solve.FMI3Model source) (entry : EventEntry.Entry) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : (signature entry) ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++ (LiteralPreparation.functions model sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare model sigs = some pool) : PreparedContract model entry sigs pool := by
  constructor
  · intro header E objects firstBlock
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    intro program actual
    apply quiet_correct header objects (pool.addresses firstBlock) model entry program
    rw [actual]
    exact LiteralPreparation.function_bound model sigs unique (signature entry) member
  · intro header before firstBlock signed objects heap frame
    obtain ⟨category, message, categoryBound, messageBound, categoryStored, messageStored, _, _⟩ :=
      (EventEntry.prepared_correct model entry sigs unique member made).failures before firstBlock signed objects heap frame
    let literals := pool.addresses firstBlock
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    have definitions : ∀ (E : Type) (program : CCalls.Events.Program E),
        program.internal = LiteralPreparation.program model sigs →
        program.internal.definitions (signature entry).name = some (.tree (Runtime.function model (signature entry))) ∧
        program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) := by
      intro E program actual
      constructor
      · rw [actual]; exact LiteralPreparation.function_bound model sigs unique (signature entry) member
      · rw [actual]; exact LiteralPreparation.helpers_bound model sigs Runtime.helpers[0] (by simp [Runtime.helpers])
    refine ⟨category, message, categoryBound, messageBound, categoryStored, messageStored, ?_, ?_⟩
    · intro E program actual
      obtain ⟨defined, helper⟩ := definitions E program actual
      exact suppressed_correct header objects literals model entry program message heap defined helper messageBound
    · intro program actual
      obtain ⟨defined, helper⟩ := definitions Invocation program actual
      exact logged_correct header objects literals model entry program category message heap signed defined helper
        categoryBound messageBound categoryStored messageStored

end Rumoca.FMI3.MEControlEnvironment.EntryControl

namespace Rumoca.FMI3.MEControlEnvironment.CompletedControl
open CTree CMemory CBody CLiteral CCalls.Events StaticFactory
open CompletedCalls

structure PreparedContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)) : Prop where
  quiet : ∀ (header : CFenv.Header) (E : Type) (objects : Objects) (firstBlock : Nat),
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : CCalls.Events.Program E),
      program.internal = LiteralPreparation.program model sigs → QuietContract program
  failures : ∀ (header : CFenv.Header) (before : Heap) (firstBlock : Nat) (signed : Bool) (objects : Objects)
    (heap : Heap), CReadOnly.Preserves (pool.install before firstBlock signed) heap →
    ∃ category messages,
      pool.addresses firstBlock "logStatus" = some category ∧
      (∀ reason, pool.addresses firstBlock (message reason) = some (messages reason)) ∧
      Stored signed heap category "logStatus" ∧
      (∀ reason, Stored signed heap (messages reason) (message reason)) ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (E : Type) (program : CCalls.Events.Program E),
         program.internal = LiteralPreparation.program model sigs → SuppressedContract program heap) ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (program : CCalls.Events.Program Invocation),
         program.internal = LiteralPreparation.program model sigs → LoggedContract program category messages heap signed)

theorem prepared_correct (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++ (LiteralPreparation.functions model sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare model sigs = some pool) : PreparedContract model sigs pool := by
  constructor
  · intro header E objects firstBlock
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    intro program actual
    apply quiet_correct header objects (pool.addresses firstBlock) model program
    rw [actual]
    exact LiteralPreparation.function_bound model sigs unique signature member
  · intro header before firstBlock signed objects heap frame
    obtain ⟨category, messages, categoryBound, messageBound, categoryStored, messageStored, _, _⟩ :=
      (CompletedCalls.prepared_correct model sigs unique member made).failures before firstBlock signed objects heap frame
    let literals := pool.addresses firstBlock
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    have definitions : ∀ (E : Type) (program : CCalls.Events.Program E),
        program.internal = LiteralPreparation.program model sigs →
        program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) ∧
        program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) := by
      intro E program actual
      constructor
      · rw [actual]; exact LiteralPreparation.function_bound model sigs unique signature member
      · rw [actual]; exact LiteralPreparation.helpers_bound model sigs Runtime.helpers[0] (by simp [Runtime.helpers])
    refine ⟨category, messages, categoryBound, messageBound, categoryStored, messageStored, ?_, ?_⟩
    · intro E program actual
      obtain ⟨defined, helper⟩ := definitions E program actual
      exact suppressed_correct header objects literals model program messages heap defined helper messageBound
    · intro program actual
      obtain ⟨defined, helper⟩ := definitions Invocation program actual
      exact logged_correct header objects literals model program category messages heap signed defined helper
        categoryBound messageBound categoryStored messageStored

end Rumoca.FMI3.MEControlEnvironment.CompletedControl

namespace Rumoca.FMI3.MEControlEnvironment.DiscreteControl
open CTree CMemory CBody CLiteral CCalls.Events StaticFactory
open DiscreteCalls

structure PreparedContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)) : Prop where
  quiet : ∀ (header : CFenv.Header) (E : Type) (objects : Objects) (firstBlock : Nat),
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : CCalls.Events.Program E),
      program.internal = LiteralPreparation.program model sigs → QuietContract program
  failures : ∀ (header : CFenv.Header) (before : Heap) (firstBlock : Nat) (signed : Bool) (objects : Objects)
    (heap : Heap), CReadOnly.Preserves (pool.install before firstBlock signed) heap →
    ∃ category messages,
      pool.addresses firstBlock "logStatus" = some category ∧
      (∀ reason, pool.addresses firstBlock (message reason) = some (messages reason)) ∧
      Stored signed heap category "logStatus" ∧
      (∀ reason, Stored signed heap (messages reason) (message reason)) ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (E : Type) (program : CCalls.Events.Program E),
         program.internal = LiteralPreparation.program model sigs → SuppressedContract program heap) ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (program : CCalls.Events.Program Invocation),
         program.internal = LiteralPreparation.program model sigs → LoggedContract program category messages heap signed)

theorem prepared_correct (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++ (LiteralPreparation.functions model sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare model sigs = some pool) : PreparedContract model sigs pool := by
  constructor
  · intro header E objects firstBlock
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    intro program actual
    apply quiet_correct header objects (pool.addresses firstBlock) model program
    rw [actual]
    exact LiteralPreparation.function_bound model sigs unique signature member
  · intro header before firstBlock signed objects heap frame
    obtain ⟨category, messages, categoryBound, messageBound, categoryStored, messageStored, _, _⟩ :=
      (DiscreteCalls.prepared_correct model sigs unique member made).failures before firstBlock signed objects heap frame
    let literals := pool.addresses firstBlock
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    have definitions : ∀ (E : Type) (program : CCalls.Events.Program E),
        program.internal = LiteralPreparation.program model sigs →
        program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) ∧
        program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) := by
      intro E program actual
      constructor
      · rw [actual]; exact LiteralPreparation.function_bound model sigs unique signature member
      · rw [actual]; exact LiteralPreparation.helpers_bound model sigs Runtime.helpers[0] (by simp [Runtime.helpers])
    refine ⟨category, messages, categoryBound, messageBound, categoryStored, messageStored, ?_, ?_⟩
    · intro E program actual
      obtain ⟨defined, helper⟩ := definitions E program actual
      exact suppressed_correct header objects literals model program messages heap defined helper messageBound
    · intro program actual
      obtain ⟨defined, helper⟩ := definitions Invocation program actual
      exact logged_correct header objects literals model program category messages heap signed defined helper
        categoryBound messageBound categoryStored messageStored

end Rumoca.FMI3.MEControlEnvironment.DiscreteControl

namespace Rumoca.FMI3.MEControlEnvironment.TimeControl
open CTree CMemory CBody CLiteral CCalls.Events StaticFactory
open TimeCalls

structure PreparedContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)) : Prop where
  quiet : ∀ (header : CFenv.Header) (E : Type) (objects : Objects) (firstBlock : Nat),
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : CCalls.Events.Program E),
      program.internal = LiteralPreparation.program model sigs → QuietContract program
  failures : ∀ (header : CFenv.Header) (before : Heap) (firstBlock : Nat) (signed : Bool) (objects : Objects)
    (heap : Heap), CReadOnly.Preserves (pool.install before firstBlock signed) heap →
    ∃ category messages,
      pool.addresses firstBlock "logStatus" = some category ∧
      (∀ reason, pool.addresses firstBlock (failureMessage reason) = some (messages reason)) ∧
      Stored signed heap category "logStatus" ∧
      (∀ reason, Stored signed heap (messages reason) (failureMessage reason)) ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (E : Type) (program : CCalls.Events.Program E),
         program.internal = LiteralPreparation.program model sigs → SuppressedContract program heap) ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (program : CCalls.Events.Program Invocation),
         program.internal = LiteralPreparation.program model sigs → LoggedContract program category messages heap signed)

theorem prepared_correct (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++ (LiteralPreparation.functions model sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare model sigs = some pool) : PreparedContract model sigs pool := by
  constructor
  · intro header E objects firstBlock
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    intro program actual
    apply RuntimeEnvironment.time_quiet header objects (pool.addresses firstBlock) model program
    rw [actual]
    exact LiteralPreparation.function_bound model sigs unique signature member
  · intro header before firstBlock signed objects heap frame
    obtain ⟨category, messages, categoryBound, messageBound, categoryStored, messageStored, _, _⟩ :=
      (TimeCalls.prepared_correct model sigs unique member made).failures before firstBlock signed objects heap frame
    let literals := pool.addresses firstBlock
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    have definitions : ∀ (E : Type) (program : CCalls.Events.Program E),
        program.internal = LiteralPreparation.program model sigs →
        program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) ∧
        program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) := by
      intro E program actual
      constructor
      · rw [actual]; exact LiteralPreparation.function_bound model sigs unique signature member
      · rw [actual]; exact LiteralPreparation.helpers_bound model sigs Runtime.helpers[0] (by simp [Runtime.helpers])
    refine ⟨category, messages, categoryBound, messageBound, categoryStored, messageStored, ?_, ?_⟩
    · intro E program actual
      obtain ⟨defined, helper⟩ := definitions E program actual
      exact suppressed_correct header objects literals model program messages heap defined helper messageBound
    · intro program actual
      obtain ⟨defined, helper⟩ := definitions Invocation program actual
      exact logged_correct header objects literals model program category messages heap signed defined helper
        categoryBound messageBound categoryStored messageStored

end Rumoca.FMI3.MEControlEnvironment.TimeControl

end
