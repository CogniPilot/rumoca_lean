import RumocaFMI3.InitializationProtocolHandoff
import RumocaFMI3.MEMixedLifecycle
import RumocaFMI3.CSRunLogging

noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CMemory

theorem MEOutputsGuarded.protects (guarded : MEOutputsGuarded objects retained addresses buffer)
    (inside : MEFailure.Protected objects addresses buffer q) : Float64Rejection.Protected objects retained q := by
  rcases inside with instanceBlock | flagsBlock | rfl | ⟨name, member, rfl⟩
  · exact Or.inl instanceBlock
  · exact Or.inr (Or.inl flagsBlock)
  · exact guarded.2
  · exact guarded.1 name member

theorem CSOutputsGuarded.protects (guarded : CSOutputsGuarded objects retained buffers)
    (inside : CSRun.Protected objects buffers q) : Float64Rejection.Protected objects retained q := by
  rcases inside with instanceBlock | flagsBlock | rfl | rfl | rfl | rfl
  · exact Or.inl instanceBlock
  · exact Or.inr (Or.inl flagsBlock)
  · exact guarded.1
  · exact guarded.2.1
  · exact guarded.2.2.1
  · exact guarded.2.2.2

theorem Retains.me_configuration [CInterface] {config : MEMixedRun.Configuration}
    (retains : Retains p before after) (stored : config.Stored before p) : config.Stored after p := by
  apply stored.framed
  intro name member
  apply retains
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> decide

theorem Retains.cs (retains : Retains p before after) : CSRun.Retains p before after :=
  fun name outside => retains name outside

/-- ME receives the flag selected by the completed initialization history.
The record update describes that configuration; it performs no new factory
call and changes neither the original callback nor its environment. -/
theorem Retention.me_created [CInterface] {config : MEMixedRun.Configuration}
    {args : FactoryArguments.Raw}
    (kept : Retention update p before after)
    (initialized : InstanceInitialization.Initialized before p .me args.environment args.logger args.logging)
    (matching : config.Matches { args with logging := update.getD args.logging }) :
    config.Stored after p := by
  have logger : load after (p.member "logger") = some (.pointer args.logger) := by
    simpa only [load, kept.fields "logger" (by decide) (by decide)] using initialized.loggerValue
  have environment : load after (p.member "environment") = some (.pointer args.environment) := by
    simpa only [load, kept.fields "environment" (by decide) (by decide)] using initialized.environmentValue
  have logging := kept.logging_value initialized.loggingValue
  cases config with
  | quiet pointer enabled =>
    change args.logger = pointer ∧ update.getD args.logging = enabled at matching
    exact ⟨by simpa only [matching.1] using logger,
      by simpa only [matching.2] using logging⟩
  | logged pointer context name effect =>
    change args.logger = some pointer ∧ update.getD args.logging = true ∧ args.environment = context at matching
    exact ⟨by simpa only [matching.1] using logger,
      by simpa only [matching.2.1, CBody.boolean] using logging,
      by simpa only [matching.2.2] using environment⟩

end Rumoca.FMI3.InitializationProtocol
end
