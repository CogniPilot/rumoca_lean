import RumocaFMI3.TensorInstanceInit

/-! Constant-rate reserved-record initialization, as a package-checked product.

The constant-rate profile (`G01`) stores only the time base, the state vector and
its writable derivative; it has no input region. The tensor reserved-record
initializer (`TensorInstanceInit.code`) writes the FMI lifecycle metadata, resets
the time base to `+0` and zero-fills the state region, and never references an
input region. It is universal in the state shape and independent of the record
profile, so the constant-rate profile's reserved record is initialized by the
same program with the same properties.

This is a package-checked product only: no production artifact is emitted, no CLI
or grammar case is added, and the tensor and scalar adapters and every existing
contract are unchanged. -/
noncomputable section
namespace Rumoca.FMI3.ConstantInstanceInit
open CTree CMemory CBody
open Rumoca.CMemory.TensorView Rumoca.CMemory.TensorRegion

/-- The constant-rate reserved-record initializer is the shared tensor
initializer; no input region is initialized. -/
def code (shape : Tensor.Shape) (kind : Kind) : List Stmt := TensorInstanceInit.code shape kind

/-- The constant-rate reserved-record initializer is closed. -/
theorem code_closed (shape : Tensor.Shape) (kind : Kind) :
    (code shape kind).all CBodyEmbedding.closedBlocks = true :=
  TensorInstanceInit.code_closed shape kind

/-- The constant-rate reserved record is initialized to the fixed-zero state fill,
the FMI lifecycle metadata and the reset time base, exactly as the tensor profile:
the initializer is profile-independent. -/
theorem initialized (heap : Heap) (p : Address) (slot : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) (shape : Tensor.Shape)
    (bounded : slot < 2 ^ 64) :
    TensorInstanceInit.Initialized heap p slot kind environment logger logging shape :=
  TensorInstanceInit.initialized heap p slot kind environment logger logging shape bounded

/-- The post-initialization state region reads the fixed-zero fill. -/
theorem reads_state (heap : Heap) (p : Address) (slot : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) (shape : Tensor.Shape) :
    Reads (TensorInstanceInit.finalHeap heap p slot kind environment logger logging shape)
      (p.member TensorInstance.stateName) (TensorReset.zeroValues shape) :=
  TensorInstanceInit.reads_state heap p slot kind environment logger logging shape

/-- Initializing one constant-rate instance leaves every cell of another instance
of the static pool untouched. -/
theorem other_instance (heap : Heap) (base : Address) (i j : Nat) (slot : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) (shape : Tensor.Shape) (query : Address)
    (different : i ≠ j) (inside : (base.index j).InRecord query) :
    TensorInstanceInit.finalHeap heap (base.index i) slot kind environment logger logging shape query
      = heap query :=
  TensorInstanceInit.other_instance heap base i j slot kind environment logger logging shape query
    different inside

end Rumoca.FMI3.ConstantInstanceInit
