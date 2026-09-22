import RumocaFMI3.PreparedStepCalls

/-! Consumable composition with a specific prepared function list and literal
pool. Signature membership/name uniqueness are discharged by constructors.
Pool construction is separately mandatory in each actual-byte adapter contract.
These fields preserve modeled callback-entry contents and outcomes, not
post-callback storage or native semantics. -/
noncomputable section
namespace Rumoca.FMI3.PreparedStep
open CTree CMemory CLiteral CBody
set_option autoImplicit false

structure TensorContractFor {source : AST.Model} {shape : Tensor.Shape}
    (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List Signature) (target : CCalls.Program) : Prop where
  lifecycleLogged : ∀ {E : Type}
    {pool : Pool (LiteralPreparation.excluded ++
      (TensorFunctions.functions model m sigs).flatMap functionNames)}
    (_made : TensorFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (_frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)),
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (outputs : StepEntry.Outputs) (point step : BitVec 64) (flag : Bool)
      (kind : Kind) (mode : Mode)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = target →
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    ¬ Reference.Allowed .doStep kind mode →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock ErrorCalls.rejectionMessage = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode heap p .terminated) message ErrorCalls.rejectionMessage ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode heap p .terminated) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point step flag outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode heap p .terminated) events value after ∧
          behavior = .terminates events ⟨.integer 3, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode heap p .terminated) events value after) ∧ behavior = .wrong [])
  outputsLogged : ∀ {E : Type}
    {pool : Pool (LiteralPreparation.excluded ++
      (TensorFunctions.functions model m sigs).flatMap functionNames)}
    (_made : TensorFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (_frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)),
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (outputs : StepEntry.Outputs) (point step : BitVec 64) (flag : Bool)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = target →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    StepArguments.MissingOutput outputs →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock "Missing output pointer" = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode heap p .terminated) message "Missing output pointer" ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode heap p .terminated) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point step flag outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode heap p .terminated) events value after ∧
          behavior = .terminates events ⟨.integer 3, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode heap p .terminated) events value after) ∧ behavior = .wrong [])
  inputsLogged : ∀ {E : Type}
    {pool : Pool (LiteralPreparation.excluded ++
      (TensorFunctions.functions model m sigs).flatMap functionNames)}
    (_made : TensorFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (_frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)),
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (buffers : StepEntry.Buffers) (point step : BitVec 64) (time : Binary64.Value) (flag : Bool)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = target →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    load heap (p.member "time") = some (.finite time) →
    StepArguments.Storage heap p buffers → ¬ StepEntry.InputsValid point step time →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock StepArguments.inputMessage = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) message StepArguments.inputMessage ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point step flag buffers.outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after ∧
          behavior = .terminates events ⟨.integer 3, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after) ∧ behavior = .wrong [])
  roundingLogged : ∀ {E : Type}
    {pool : Pool (LiteralPreparation.excluded ++
      (TensorFunctions.functions model m sigs).flatMap functionNames)}
    (_made : TensorFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (_frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)) (header : CFenv.Header),
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (buffers : StepEntry.Buffers) (point step : BitVec 64) (time : Binary64.Value)
      (flag : Bool) (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
      (integer : context.target.types "int" = some .int32)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = target →
    context.target.constants "fegetround" = none →
    context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
    program.externals "fegetround" = some (CMathCalls.roundingExternal integer observed range) →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    load heap (p.member "time") = some (.finite time) →
    StepArguments.Storage heap p buffers → StepEntry.InputsValid point step time →
    observed ≠ header.nearest →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock StepFailures.roundingMessage = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) message StepFailures.roundingMessage ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point step flag buffers.outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after ∧
          behavior = .terminates events ⟨.integer 3, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after) ∧ behavior = .wrong [])
  stopLogged : ∀ {E : Type}
    {pool : Pool (LiteralPreparation.excluded ++
      (TensorFunctions.functions model m sigs).flatMap functionNames)}
    (_made : TensorFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (_frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)) (header : CFenv.Header),
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (buffers : StepEntry.Buffers) (point : BitVec 64) (step time : Binary64.Value)
      (flag : Bool) (stop : Option Binary64.Value)
      (integer : context.target.types "int" = some .int32)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = target →
    context.target.constants "fegetround" = none →
    context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
    program.externals "fegetround" = some (CMathCalls.roundingExternal integer header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    load heap (p.member "time") = some (.finite time) →
    StepArguments.Storage heap p buffers → StepEntry.InputsValid point (Binary64.toBits step).val time →
    load heap (p.member "stopDefined") = some (boolean stop.isSome) →
    (∀ value, stop = some value → load heap (p.member "stop") = some (.finite value)) →
    StepGuards.AboveStop (Binary64.addResult time step) stop →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock StepFailures.stopMessage = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) message StepFailures.stopMessage ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point (Binary64.toBits step).val flag buffers.outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after ∧
          behavior = .terminates events ⟨.integer 3, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after) ∧ behavior = .wrong [])
  discardLogged : ∀ {E : Type}
    {pool : Pool (LiteralPreparation.excluded ++
      (TensorFunctions.functions model m sigs).flatMap functionNames)}
    (_made : TensorFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (_frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)) (header : CFenv.Header),
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (buffers : StepEntry.Buffers) (point : BitVec 64) (step time : Binary64.Value)
      (flag : Bool) (stop : Option Binary64.Value)
      (integer : context.target.types "int" = some .int32)
      (double : context.target.types "double" = some .float64)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = target →
    context.target.constants "fegetround" = none →
    context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
    context.target.constants "fmi3Discard" = some (.integer 2) →
    program.externals "fegetround" = some (CMathCalls.roundingExternal integer header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
    (StepGuards.Progress time (Binary64.addResult time step) →
      context.target.constants "floor" = none ∧
      program.externals "floor" = some (CMathCalls.floorExternal double)) →
    load heap (p.member "kind") = some (.integer 1) →
    load heap (p.member "mode") = some (.integer 4) →
    load heap (p.member "time") = some (.finite time) →
    StepArguments.Storage heap p buffers → StepEntry.InputsValid point (Binary64.toBits step).val time →
    load heap (p.member "stopDefined") = some (boolean stop.isSome) →
    (∀ value, stop = some value → load heap (p.member "stop") = some (.finite value)) →
    ¬ StepGuards.AboveStop (Binary64.addResult time step) stop →
    StepDiscard.Rejected time step →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock StepDiscard.message = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (StepEntry.outputHeap heap buffers time) message StepDiscard.message ∧
      StoredContents signed (pool.install before firstBlock signed)
        (StepEntry.outputHeap heap buffers time) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point (Binary64.toBits step).val flag buffers.outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (StepDiscard.arguments environment category message)
          (StepEntry.outputHeap heap buffers time) events value after ∧
          behavior = .terminates events ⟨.integer 2, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (StepDiscard.arguments environment category message)
          (StepEntry.outputHeap heap buffers time) events value after) ∧ behavior = .wrong [])

structure TensorContract {source : AST.Model} {shape : Tensor.Shape}
    (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List Signature) : Prop where
  lifecycleLogged : ∀ {E : Type}
    {pool : Pool (LiteralPreparation.excluded ++
      (TensorFunctions.functions model m sigs).flatMap functionNames)}
    (_made : TensorFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (_frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)),
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (outputs : StepEntry.Outputs) (point step : BitVec 64) (flag : Bool)
      (kind : Kind) (mode : Mode)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = TensorFunctions.program model m sigs →
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    ¬ Reference.Allowed .doStep kind mode →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock ErrorCalls.rejectionMessage = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode heap p .terminated) message ErrorCalls.rejectionMessage ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode heap p .terminated) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point step flag outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode heap p .terminated) events value after ∧
          behavior = .terminates events ⟨.integer 3, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode heap p .terminated) events value after) ∧ behavior = .wrong [])
  outputsLogged : ∀ {E : Type}
    {pool : Pool (LiteralPreparation.excluded ++
      (TensorFunctions.functions model m sigs).flatMap functionNames)}
    (_made : TensorFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (_frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)),
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (outputs : StepEntry.Outputs) (point step : BitVec 64) (flag : Bool)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = TensorFunctions.program model m sigs →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    StepArguments.MissingOutput outputs →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock "Missing output pointer" = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode heap p .terminated) message "Missing output pointer" ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode heap p .terminated) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point step flag outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode heap p .terminated) events value after ∧
          behavior = .terminates events ⟨.integer 3, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode heap p .terminated) events value after) ∧ behavior = .wrong [])
  inputsLogged : ∀ {E : Type}
    {pool : Pool (LiteralPreparation.excluded ++
      (TensorFunctions.functions model m sigs).flatMap functionNames)}
    (_made : TensorFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (_frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)),
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (buffers : StepEntry.Buffers) (point step : BitVec 64) (time : Binary64.Value) (flag : Bool)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = TensorFunctions.program model m sigs →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    load heap (p.member "time") = some (.finite time) →
    StepArguments.Storage heap p buffers → ¬ StepEntry.InputsValid point step time →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock StepArguments.inputMessage = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) message StepArguments.inputMessage ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point step flag buffers.outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after ∧
          behavior = .terminates events ⟨.integer 3, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after) ∧ behavior = .wrong [])
  roundingLogged : ∀ {E : Type}
    {pool : Pool (LiteralPreparation.excluded ++
      (TensorFunctions.functions model m sigs).flatMap functionNames)}
    (_made : TensorFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (_frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)) (header : CFenv.Header),
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (buffers : StepEntry.Buffers) (point step : BitVec 64) (time : Binary64.Value)
      (flag : Bool) (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
      (integer : context.target.types "int" = some .int32)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = TensorFunctions.program model m sigs →
    context.target.constants "fegetround" = none →
    context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
    program.externals "fegetround" = some (CMathCalls.roundingExternal integer observed range) →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    load heap (p.member "time") = some (.finite time) →
    StepArguments.Storage heap p buffers → StepEntry.InputsValid point step time →
    observed ≠ header.nearest →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock StepFailures.roundingMessage = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) message StepFailures.roundingMessage ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point step flag buffers.outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after ∧
          behavior = .terminates events ⟨.integer 3, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after) ∧ behavior = .wrong [])
  stopLogged : ∀ {E : Type}
    {pool : Pool (LiteralPreparation.excluded ++
      (TensorFunctions.functions model m sigs).flatMap functionNames)}
    (_made : TensorFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (_frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)) (header : CFenv.Header),
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (buffers : StepEntry.Buffers) (point : BitVec 64) (step time : Binary64.Value)
      (flag : Bool) (stop : Option Binary64.Value)
      (integer : context.target.types "int" = some .int32)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = TensorFunctions.program model m sigs →
    context.target.constants "fegetround" = none →
    context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
    program.externals "fegetround" = some (CMathCalls.roundingExternal integer header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    load heap (p.member "time") = some (.finite time) →
    StepArguments.Storage heap p buffers → StepEntry.InputsValid point (Binary64.toBits step).val time →
    load heap (p.member "stopDefined") = some (boolean stop.isSome) →
    (∀ value, stop = some value → load heap (p.member "stop") = some (.finite value)) →
    StepGuards.AboveStop (Binary64.addResult time step) stop →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock StepFailures.stopMessage = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) message StepFailures.stopMessage ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point (Binary64.toBits step).val flag buffers.outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after ∧
          behavior = .terminates events ⟨.integer 3, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after) ∧ behavior = .wrong [])
  discardLogged : ∀ {E : Type}
    {pool : Pool (LiteralPreparation.excluded ++
      (TensorFunctions.functions model m sigs).flatMap functionNames)}
    (_made : TensorFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (_frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)) (header : CFenv.Header),
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (buffers : StepEntry.Buffers) (point : BitVec 64) (step time : Binary64.Value)
      (flag : Bool) (stop : Option Binary64.Value)
      (integer : context.target.types "int" = some .int32)
      (double : context.target.types "double" = some .float64)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = TensorFunctions.program model m sigs →
    context.target.constants "fegetround" = none →
    context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
    context.target.constants "fmi3Discard" = some (.integer 2) →
    program.externals "fegetround" = some (CMathCalls.roundingExternal integer header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
    (StepGuards.Progress time (Binary64.addResult time step) →
      context.target.constants "floor" = none ∧
      program.externals "floor" = some (CMathCalls.floorExternal double)) →
    load heap (p.member "kind") = some (.integer 1) →
    load heap (p.member "mode") = some (.integer 4) →
    load heap (p.member "time") = some (.finite time) →
    StepArguments.Storage heap p buffers → StepEntry.InputsValid point (Binary64.toBits step).val time →
    load heap (p.member "stopDefined") = some (boolean stop.isSome) →
    (∀ value, stop = some value → load heap (p.member "stop") = some (.finite value)) →
    ¬ StepGuards.AboveStop (Binary64.addResult time step) stop →
    StepDiscard.Rejected time step →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock StepDiscard.message = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (StepEntry.outputHeap heap buffers time) message StepDiscard.message ∧
      StoredContents signed (pool.install before firstBlock signed)
        (StepEntry.outputHeap heap buffers time) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point (Binary64.toBits step).val flag buffers.outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (StepDiscard.arguments environment category message)
          (StepEntry.outputHeap heap buffers time) events value after ∧
          behavior = .terminates events ⟨.integer 2, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (StepDiscard.arguments environment category message)
          (StepEntry.outputHeap heap buffers time) events value after) ∧ behavior = .wrong [])

theorem tensor_contract_for {source : AST.Model} {shape : Tensor.Shape}
    (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List Signature) (stepMember : StepEntry.signature ∈ sigs)
    (target : CCalls.Program)
    (stepDefinition : target.definitions "fmi3DoStep" = some (.tree (TensorDoStep.function shape m.hasOutput)))
    (failureDefinition : target.definitions "fail" = some (.tree Runtime.helpers[0])) :
    TensorContractFor model m sigs target where
  lifecycleLogged := fun {E} => PreparedLifecycleFailureCall.tensor_logged_for (E := E)
    model m sigs stepMember target stepDefinition failureDefinition
  outputsLogged := fun {E} => PreparedOutputFailureCall.tensor_logged_for (E := E)
    model m sigs stepMember target stepDefinition failureDefinition
  inputsLogged := fun {E} => PreparedInputFailureCall.tensor_logged_for (E := E)
    model m sigs stepMember target stepDefinition failureDefinition
  roundingLogged := fun {E} => PreparedNumericFailureCall.tensor_rounding_logged_for (E := E)
    model m sigs stepMember target stepDefinition failureDefinition
  stopLogged := fun {E} => PreparedNumericFailureCall.tensor_stop_logged_for (E := E)
    model m sigs stepMember target stepDefinition failureDefinition
  discardLogged := fun {E} => PreparedNumericFailureCall.tensor_discard_logged_for (E := E)
    model m sigs stepMember target stepDefinition

theorem tensor_contract {source : AST.Model} {shape : Tensor.Shape}
    (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List Signature) (stepMember : StepEntry.signature ∈ sigs)
    (unique : ((TensorFunctions.functions model m sigs).map (fun fn => fn.signature.name)).Nodup) :
    TensorContract model m sigs := by
  have checked := tensor_contract_for model m sigs stepMember (TensorFunctions.program model m sigs)
    (TensorFunctions.doStep_bound model m sigs unique stepMember)
    (TensorFunctions.helpers_bound model m sigs Runtime.helpers[0] (by simp [TensorFunctions.helpers]))
  exact ⟨checked.lifecycleLogged, checked.outputsLogged, checked.inputsLogged,
    checked.roundingLogged, checked.stopLogged, checked.discardLogged⟩

structure ConstantContract {source : AST.Model} {n : Nat}
    (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature) : Prop where
  lifecycleLogged : ∀ {E : Type}
    {pool : Pool (LiteralPreparation.excluded ++
      (ConstantFunctions.functions model m sigs).flatMap functionNames)}
    (_made : ConstantFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (_frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)),
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (outputs : StepEntry.Outputs) (point step : BitVec 64) (flag : Bool)
      (kind : Kind) (mode : Mode)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = ConstantFunctions.program model m sigs →
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    ¬ Reference.Allowed .doStep kind mode →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock ErrorCalls.rejectionMessage = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode heap p .terminated) message ErrorCalls.rejectionMessage ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode heap p .terminated) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point step flag outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode heap p .terminated) events value after ∧
          behavior = .terminates events ⟨.integer 3, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode heap p .terminated) events value after) ∧ behavior = .wrong [])
  outputsLogged : ∀ {E : Type}
    {pool : Pool (LiteralPreparation.excluded ++
      (ConstantFunctions.functions model m sigs).flatMap functionNames)}
    (_made : ConstantFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (_frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)),
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (outputs : StepEntry.Outputs) (point step : BitVec 64) (flag : Bool)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = ConstantFunctions.program model m sigs →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    StepArguments.MissingOutput outputs →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock "Missing output pointer" = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode heap p .terminated) message "Missing output pointer" ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode heap p .terminated) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point step flag outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode heap p .terminated) events value after ∧
          behavior = .terminates events ⟨.integer 3, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode heap p .terminated) events value after) ∧ behavior = .wrong [])
  inputsLogged : ∀ {E : Type}
    {pool : Pool (LiteralPreparation.excluded ++
      (ConstantFunctions.functions model m sigs).flatMap functionNames)}
    (_made : ConstantFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (_frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)),
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (buffers : StepEntry.Buffers) (point step : BitVec 64) (time : Binary64.Value) (flag : Bool)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = ConstantFunctions.program model m sigs →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    load heap (p.member "time") = some (.finite time) →
    StepArguments.Storage heap p buffers → ¬ StepEntry.InputsValid point step time →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock StepArguments.inputMessage = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) message StepArguments.inputMessage ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point step flag buffers.outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after ∧
          behavior = .terminates events ⟨.integer 3, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after) ∧ behavior = .wrong [])
  roundingLogged : ∀ {E : Type}
    {pool : Pool (LiteralPreparation.excluded ++
      (ConstantFunctions.functions model m sigs).flatMap functionNames)}
    (_made : ConstantFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (_frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)) (header : CFenv.Header),
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (buffers : StepEntry.Buffers) (point step : BitVec 64) (time : Binary64.Value)
      (flag : Bool) (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
      (integer : context.target.types "int" = some .int32)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = ConstantFunctions.program model m sigs →
    context.target.constants "fegetround" = none →
    context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
    program.externals "fegetround" = some (CMathCalls.roundingExternal integer observed range) →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    load heap (p.member "time") = some (.finite time) →
    StepArguments.Storage heap p buffers → StepEntry.InputsValid point step time →
    observed ≠ header.nearest →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock StepFailures.roundingMessage = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) message StepFailures.roundingMessage ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point step flag buffers.outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after ∧
          behavior = .terminates events ⟨.integer 3, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after) ∧ behavior = .wrong [])
  stopLogged : ∀ {E : Type}
    {pool : Pool (LiteralPreparation.excluded ++
      (ConstantFunctions.functions model m sigs).flatMap functionNames)}
    (_made : ConstantFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (_frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)) (header : CFenv.Header),
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (buffers : StepEntry.Buffers) (point : BitVec 64) (step time : Binary64.Value)
      (flag : Bool) (stop : Option Binary64.Value)
      (integer : context.target.types "int" = some .int32)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = ConstantFunctions.program model m sigs →
    context.target.constants "fegetround" = none →
    context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
    program.externals "fegetround" = some (CMathCalls.roundingExternal integer header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    load heap (p.member "time") = some (.finite time) →
    StepArguments.Storage heap p buffers → StepEntry.InputsValid point (Binary64.toBits step).val time →
    load heap (p.member "stopDefined") = some (boolean stop.isSome) →
    (∀ value, stop = some value → load heap (p.member "stop") = some (.finite value)) →
    StepGuards.AboveStop (Binary64.addResult time step) stop →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock StepFailures.stopMessage = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) message StepFailures.stopMessage ∧
      StoredContents signed (pool.install before firstBlock signed)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point (Binary64.toBits step).val flag buffers.outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after ∧
          behavior = .terminates events ⟨.integer 3, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
          (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after) ∧ behavior = .wrong [])
  discardLogged : ∀ {E : Type}
    {pool : Pool (LiteralPreparation.excluded ++
      (ConstantFunctions.functions model m sigs).flatMap functionNames)}
    (_made : ConstantFunctions.prepare model m sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (_frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (context : ErrorContext (pool.addresses firstBlock)) (header : CFenv.Header),
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p logger : Address)
      (buffers : StepEntry.Buffers) (point : BitVec 64) (step time : Binary64.Value)
      (flag : Bool) (stop : Option Binary64.Value)
      (integer : context.target.types "int" = some .int32)
      (double : context.target.types "double" = some .float64)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal = ConstantFunctions.program model m sigs →
    context.target.constants "fegetround" = none →
    context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
    context.target.constants "fmi3Discard" = some (.integer 2) →
    program.externals "fegetround" = some (CMathCalls.roundingExternal integer header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
    (StepGuards.Progress time (Binary64.addResult time step) →
      context.target.constants "floor" = none ∧
      program.externals "floor" = some (CMathCalls.floorExternal double)) →
    load heap (p.member "kind") = some (.integer 1) →
    load heap (p.member "mode") = some (.integer 4) →
    load heap (p.member "time") = some (.finite time) →
    StepArguments.Storage heap p buffers → StepEntry.InputsValid point (Binary64.toBits step).val time →
    load heap (p.member "stopDefined") = some (boolean stop.isSome) →
    (∀ value, stop = some value → load heap (p.member "stop") = some (.finite value)) →
    ¬ StepGuards.AboveStop (Binary64.addResult time step) stop →
    StepDiscard.Rejected time step →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∃ message category : Address,
      pool.addresses firstBlock StepDiscard.message = some message ∧
      pool.addresses firstBlock "logStatus" = some category ∧
      StoredContents signed (pool.install before firstBlock signed)
        (StepEntry.outputHeap heap buffers time) message StepDiscard.message ∧
      StoredContents signed (pool.install before firstBlock signed)
        (StepEntry.outputHeap heap buffers time) category "logStatus" ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some p) point (Binary64.toBits step).val flag buffers.outputs) heap .done) behavior ↔
        (∃ events value after, foreign.execute (StepDiscard.arguments environment category message)
          (StepEntry.outputHeap heap buffers time) events value after ∧
          behavior = .terminates events ⟨.integer 2, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (StepDiscard.arguments environment category message)
          (StepEntry.outputHeap heap buffers time) events value after) ∧ behavior = .wrong [])

theorem constant_contract {source : AST.Model} {n : Nat}
    (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature) (stepMember : StepEntry.signature ∈ sigs)
    (unique : ((ConstantFunctions.functions model m sigs).map (fun fn => fn.signature.name)).Nodup) :
    ConstantContract model m sigs where
  lifecycleLogged := fun {E} => PreparedLifecycleFailureCall.constant_logged (E := E) model m sigs stepMember unique
  outputsLogged := fun {E} => PreparedOutputFailureCall.constant_logged (E := E) model m sigs stepMember unique
  inputsLogged := fun {E} => PreparedInputFailureCall.constant_logged (E := E) model m sigs stepMember unique
  roundingLogged := fun {E} => PreparedNumericFailureCall.constant_rounding_logged (E := E) model m sigs stepMember unique
  stopLogged := fun {E} => PreparedNumericFailureCall.constant_stop_logged (E := E) model m sigs stepMember unique
  discardLogged := fun {E} => PreparedNumericFailureCall.constant_discard_logged (E := E) model m sigs stepMember unique

end Rumoca.FMI3.PreparedStep
