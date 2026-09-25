import RumocaFMI3.TensorInstanceInit

/-! Constant-rate reserved-record initialization, as a package-checked product.

The constant-rate profile (`G01`) stores the time base, the state vector and its
writable derivative; it has no input region and no output region. Its record
layout is the profile-generic layout without them (`TensorStorage.regions shape
false false`), and the shared initializer (`TensorInstanceInit.code`) runs over
exactly that region list: it records the handle members, zero-fills the state and
derivative regions and resets every restored scalar, as the tensor profile does.

This is a package-checked product only: no production artifact is emitted, no CLI
or grammar case is added. -/
noncomputable section
namespace Rumoca.FMI3.ConstantInstanceInit
open CTree CMemory CBody
open Rumoca.CMemory.TensorView Rumoca.CMemory.TensorRegion

/-- The constant-rate record regions: the state and the derivative. -/
def regions (shape : Tensor.Shape) : TensorReset.Regions := TensorStorage.regions shape false false

/-- The constant-rate reserved-record initializer is the shared initializer over the
constant-rate regions. -/
def code (shape : Tensor.Shape) (kind : Kind) : List Stmt := TensorInstanceInit.code (regions shape) kind

/-- The constant-rate reserved-record initializer is closed. -/
theorem code_closed (shape : Tensor.Shape) (kind : Kind) :
    (code shape kind).all CBodyEmbedding.closedBlocks = true :=
  TensorInstanceInit.code_closed (regions shape) kind

/-- The constant-rate reserved record is initialized to the restored values: the
handle members, the fixed-zero state and derivative, and every restored scalar. -/
theorem initialized (heap : Heap) (p : Address) (slot : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) (shape : Tensor.Shape)
    (bounded : slot < 2 ^ 64) :
    TensorInstanceInit.Initialized heap p slot kind environment logger logging (regions shape) :=
  TensorInstanceInit.initialized heap p slot kind environment logger logging (regions shape)
    (TensorStorage.regions_distinct shape false false) bounded

/-- The post-initialization state region reads the fixed-zero fill. -/
theorem reads_state (heap : Heap) (p : Address) (slot : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) (shape : Tensor.Shape) :
    Reads (TensorInstanceInit.finalHeap heap p slot kind environment logger logging (regions shape))
      (p.member TensorInstance.stateName) (TensorReset.zeroValues shape) :=
  TensorReset.restoreHeap_reads _ p (regions shape) (TensorStorage.regions_distinct shape false false)
    (TensorInstance.stateName, shape) (by simp [regions, TensorStorage.regions])

/-- The post-initialization derivative region reads the fixed-zero fill. -/
theorem reads_derivative (heap : Heap) (p : Address) (slot : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) (shape : Tensor.Shape) :
    Reads (TensorInstanceInit.finalHeap heap p slot kind environment logger logging (regions shape))
      (p.member TensorInstance.derivativeName) (TensorReset.zeroValues shape) :=
  TensorReset.restoreHeap_reads _ p (regions shape) (TensorStorage.regions_distinct shape false false)
    (TensorInstance.derivativeName, shape) (by simp [regions, TensorStorage.regions])

/-- Initializing one constant-rate instance leaves every cell of another instance
of the static pool untouched. -/
theorem other_instance (heap : Heap) (base : Address) (i j : Nat) (slot : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) (shape : Tensor.Shape) (query : Address)
    (different : i ≠ j) (inside : (base.index j).InRecord query) :
    TensorInstanceInit.finalHeap heap (base.index i) slot kind environment logger logging (regions shape) query
      = heap query :=
  TensorInstanceInit.other_instance heap base i j slot kind environment logger
    logging (regions shape) query different inside

end Rumoca.FMI3.ConstantInstanceInit
