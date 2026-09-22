import RumocaFMI3.TensorDoStep
import RumocaFMI3.RuntimeEnvironment
import RumocaC.TensorProgramCalls

/-! Actual numerical header facts for the FMI static, fenv and runtime interfaces.
These use the owning CInterface dictionary, including the two numerical-pointer
spellings. No alternate dictionary or helper definitions are supplied here.
The modeled bindings do not establish the native ABI or native fenv behavior. -/
namespace Rumoca.FMI3.TensorHeader
open CMemory CTensor.Lowering Solve.Tensor

theorem double_pointer : cTypes "double *" = some .pointer := rfl

theorem const_double_pointer : cTypes "const double *" = some .pointer := rfl

theorem static_binary (literals : CLiteralAddresses) : CTensor.HeaderTypes (cInterface literals) :=
  ⟨rfl, rfl, rfl⟩

theorem static_fill (literals : CLiteralAddresses) : CTensor.Fill.HeaderTypes (cInterface literals) :=
  ⟨rfl, rfl, rfl⟩

theorem fenv_binary (header : CFenv.Header) (literals : CLiteralAddresses) :
    CTensor.HeaderTypes (header.interface (cInterface literals)) := ⟨rfl, rfl, rfl⟩

theorem fenv_fill (header : CFenv.Header) (literals : CLiteralAddresses) :
    CTensor.Fill.HeaderTypes (header.interface (cInterface literals)) := ⟨rfl, rfl, rfl⟩

theorem runtime_binary (header : CFenv.Header) (objects : StaticFactory.Objects)
    (literals : CLiteralAddresses) : CTensor.HeaderTypes (RuntimeEnvironment.interface header objects literals) := ⟨rfl, rfl, rfl⟩

theorem runtime_fill (header : CFenv.Header) (objects : StaticFactory.Objects)
    (literals : CLiteralAddresses) : CTensor.Fill.HeaderTypes (RuntimeEnvironment.interface header objects literals) := ⟨rfl, rfl, rfl⟩

theorem fenv_step_types (header : CFenv.Header) (literals : CLiteralAddresses) :
    @StepEntry.Types (header.interface (cInterface literals)) := by
  letI : CInterface := header.interface (cInterface literals)
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem runtime_step_types (header : CFenv.Header) (objects : StaticFactory.Objects)
    (literals : CLiteralAddresses) : @StepEntry.Types (RuntimeEnvironment.interface header objects literals) := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem fenv_nearest (header : CFenv.Header) (literals : CLiteralAddresses) :
    (header.interface (cInterface literals)).constants "FE_TONEAREST" = some (.integer header.nearest) :=
  CFenv.Header.nearest_binding _ _

theorem runtime_nearest (header : CFenv.Header) (objects : StaticFactory.Objects)
    (literals : CLiteralAddresses) :
    (RuntimeEnvironment.interface header objects literals).constants "FE_TONEAREST" = some (.integer header.nearest) :=
  CFenv.Header.nearest_binding _ _

theorem fenv_tensor (header : CFenv.Header) (literals : CLiteralAddresses) :
    TensorDoStep.TensorFenv (header.interface (cInterface literals)) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [CFenv.Header.other_binding header _ _ (by decide)]; rfl

theorem runtime_tensor (header : CFenv.Header) (objects : StaticFactory.Objects)
    (literals : CLiteralAddresses) : TensorDoStep.TensorFenv (RuntimeEnvironment.interface header objects literals) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  all_goals change (header.interface (StaticFactory.executionInterface objects literals)).constants _ = _
  all_goals rw [CFenv.Header.other_binding header _ _ (by decide)]; rfl

theorem static_library (literals : CLiteralAddresses) (p : Program Γ shape)
    (definitions : CLoops.Calls.Definitions)
    (binary : ∀ op ∈ requiredOps p, definitions (CTensor.function op).signature.name = some (CTensor.function op))
    (fill : definitions CTensor.Fill.function.signature.name = some CTensor.Fill.function) :
    letI : CInterface := cInterface literals
    LibraryFor p definitions := by
  letI : CInterface := cInterface literals
  exact ⟨static_binary literals, static_fill literals, binary, fill⟩

theorem fenv_library (header : CFenv.Header) (literals : CLiteralAddresses) (p : Program Γ shape)
    (definitions : CLoops.Calls.Definitions)
    (binary : ∀ op ∈ requiredOps p, definitions (CTensor.function op).signature.name = some (CTensor.function op))
    (fill : definitions CTensor.Fill.function.signature.name = some CTensor.Fill.function) :
    letI : CInterface := header.interface (cInterface literals)
    LibraryFor p definitions := by
  letI : CInterface := header.interface (cInterface literals)
  exact ⟨fenv_binary header literals, fenv_fill header literals, binary, fill⟩

theorem runtime_library (header : CFenv.Header) (objects : StaticFactory.Objects)
    (literals : CLiteralAddresses) (p : Program Γ shape) (definitions : CLoops.Calls.Definitions)
    (binary : ∀ op ∈ requiredOps p, definitions (CTensor.function op).signature.name = some (CTensor.function op))
    (fill : definitions CTensor.Fill.function.signature.name = some CTensor.Fill.function) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    LibraryFor p definitions := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  exact ⟨runtime_binary header objects literals, runtime_fill header objects literals, binary, fill⟩

end Rumoca.FMI3.TensorHeader
