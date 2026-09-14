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

end Rumoca.FMI3.InitializationProtocol
end
