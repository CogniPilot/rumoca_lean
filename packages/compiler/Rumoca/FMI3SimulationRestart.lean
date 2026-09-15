import Rumoca.FMI3InitializationRestart
import RumocaFMI3.CSRunCompleted

noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CMemory StaticFactory CCalls.Events

variable {source : AST.Model} {model : Solve.FMI3Model source}
variable {readers : ReadBank}

/-- A completed mixed ME history supplies every reset/reinitialization
premise. The new protocol uses the original caller bank and source contract. -/
theorem restart_after_me [CInterface] {program : Program Invocation}
    {objects : Objects} {owners : SlotOwners.State objects.capacity} {config : MEMixedRun.Configuration}
    (reset : StaticReset.ExecutionContract program)
    (certified : MEMixedRun.Trace model objects owners config program p addresses buffer
      heap reference clock simulation final finalClock)
    (executed : MEMixedRun.Completed program p addresses buffer heap simulation observed after epochs)
    (initial : MENumericalHistory.Stored heap p clock reference addresses buffer)
    (inPool : p.block = objects.instances.block)
    (caller : CallerStorage objects retained original heap)
    (literalFrame : CReadOnly.Preserves literals heap) (logging : LogPolicy program objects retained heap p)
    (policy : config.StoragePolicy (Float64Rejection.Protected objects retained))
    (readerFrame : readers.Frame original heap)
    (readerPolicy : config.FramePolicy readers.Region)
    (readerOutside : ∀ q, readers.Region q → ¬ p.InRecord q ∧ MENumericalRun.Outside p addresses buffer q)
    (readerSafe : ∀ action ∈ simulation, ∀ q, readers.Region q → ¬ action.CallerRegion q)
    (compileProtocol : ∀ next, Invariant program objects retained owners original literals next p .me State.reset readers →
      SourceContract model program objects retained owners original literals next p access .me State.reset nextState actions readers) :
    RestartSourceContract model program objects retained owners original literals after p access .me nextState actions readers := by
  obtain ⟨stored, resetStorage, _, represented, readonly, frame⟩ := certified.completed executed
  have loggingAfter := logging.fields (fun name member =>
    frame _ (Or.inl inPool) (MEMixedRun.configuration_outside initial name
      (by simpa using List.mem_append_left ["slot"] member)))
  exact restart_source model reset resetStorage stored.control.kind stored.mode_loaded represented
    (caller.trans (certified.storage executed policy)) (literalFrame.trans readonly) loggingAfter
    (readerFrame.trans (fun q inside => certified.callerFrame executed readerPolicy q inside
      (readerOutside q inside).2 (fun action member => readerSafe action member q inside)))
    (fun q inside => (readerOutside q inside).1) compileProtocol

/-- Every returning logged CS branch can reset and run the same reusable
initialization protocol, without presuming a callback return or later storage. -/
theorem restart_after_cs_logged [CInterface] {program : Program Invocation}
    {objects : Objects} {owners : SlotOwners.State objects.capacity} {logger : CSRun.Logger}
    (reset : StaticReset.ExecutionContract program)
    (certified : CSRun.LoggedTrace objects logger owners model.solve program p buffers heap reference simulation final statuses)
    (executed : CSRun.Completed program p heap simulation observed events after)
    (caller : CallerStorage objects retained original heap)
    (literalFrame : CReadOnly.Preserves literals heap) (logging : LogPolicy program objects retained heap p)
    (policy : logger.StoragePolicy (Float64Rejection.Protected objects retained))
    (readerFrame : readers.Frame original heap)
    (readerPolicy : logger.FramePolicy readers.Region)
    (readerOutside : ∀ q, readers.Region q → CSRun.Outside p buffers q)
    (compileProtocol : ∀ next, Invariant program objects retained owners original literals next p .cs State.reset readers →
      SourceContract model program objects retained owners original literals next p access .cs State.reset nextState actions readers) :
    RestartSourceContract model program objects retained owners original literals after p access .cs nextState actions readers := by
  have same := certified.statuses_eq executed
  subst observed
  obtain ⟨stored, _, represented, keeps, readonly, _⟩ := certified.completed executed
  exact restart_source model reset stored.reset stored.kind stored.mode represented
    (caller.trans (certified.storage executed policy)) (literalFrame.trans readonly)
    (logging.framed (fun name outside => keeps name outside))
    (readerFrame.trans (fun q inside => certified.frame executed readerPolicy q inside (readerOutside q inside)))
    (fun q inside => (readerOutside q inside).1) compileProtocol

/-- The suppressed CS certificate derives the same restart obligations and
determines every raw completed history's final heap and statuses. -/
theorem restart_after_cs_suppressed [CInterface] {program : Program Invocation}
    {objects : Objects} {owners : SlotOwners.State objects.capacity}
    (reset : StaticReset.ExecutionContract program)
    (certified : CSRun.Calls model.solve program p buffers heap reference simulation expectedHeap final statuses)
    (executed : CSRun.Completed program p heap simulation observed events after)
    (initial : CSRun.Stored model.solve heap p buffers reference)
    (represented : SlotOwners.Represents objects.flagsBlock heap owners)
    (caller : CallerStorage objects retained original heap)
    (literalFrame : CReadOnly.Preserves literals heap) (logging : LogPolicy program objects retained heap p)
    (readerFrame : readers.Frame original heap)
    (readerOutside : ∀ q, readers.Region q → CSRun.Outside p buffers q)
    (compileProtocol : ∀ next, Invariant program objects retained owners original literals next p .cs State.reset readers →
      SourceContract model program objects retained owners original literals next p access .cs State.reset nextState actions readers) :
    RestartSourceContract model program objects retained owners original literals after p access .cs nextState actions readers := by
  obtain ⟨_, _, same⟩ := certified.determines executed
  subst after
  have stored := certified.stored initial
  exact restart_source model reset stored.reset stored.kind stored.mode
    (SlotOwners.ordinary_preserves represented certified.atomic)
    (caller.trans (CallerStorage.ordinary certified.storage)) (literalFrame.trans certified.readonly)
    (logging.framed (fun name outside => certified.retains name outside))
    (readerFrame.trans (fun q inside => certified.frame q (readerOutside q inside)))
    (fun q inside => (readerOutside q inside).1) compileProtocol

end Rumoca.FMI3.InitializationProtocol
end
