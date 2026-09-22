import RumocaEFMI.TensorMethodEntry
import RumocaEFMI.TensorPublicStorage

/-! Complete allocated-only Startup/Recalibrate on the canonical contextual
ten-tree machine with the actual eFMI interface. No source contract or native execution. -/
noncomputable section
namespace Rumoca.EFMI.AllocatedMethods
open CTree CMemory CMemory.TensorView CDeclaredMembers CDeclaredMembers.MemberStorage
open CTensor CTensor.ProgramFixture Solve.Tensor
open TensorProduction TensorPublicStorage TensorNumericalLinkage
open CContextMachine TensorContextCalls

theorem allocated_frame {shape : Tensor.Shape} {before after : Heap} {base : Address}
    (storage : ArrayStorage before base .float64 shape)
    (frame : ∀ i, after (base.index i) = before (base.index i)) :
    ArrayStorage after base .float64 shape := by
  refine ⟨storage.1, ?_⟩
  intro i
  obtain ⟨cell, found, typed⟩ := storage.2 i
  exact ⟨cell, (frame i.val).trans found, typed⟩

theorem after_initial (storage : AllocatedStorage objects heap base)
    (writes : Writable after (base.member squareVar.name) squareShape.volume)
    (frame : ∀ q, (∀ i < squareShape.volume, q ≠ (base.member squareVar.name).index i) →
      after q = heap q) : AllocatedStorage objects after base := by
  refine ⟨storage.object, ?_, writes, ?_, ?_, ?_⟩
  · exact allocated_frame storage.input (PublicRHS.member_preserved frame (by decide +kernel))
  · exact writable_framed storage.jacobian (PublicRHS.member_preserved frame (by decide +kernel))
  · apply storage.clock.framed
    simpa only [Address.index_zero] using PublicRHS.member_preserved frame
      (show clockName ≠ squareVar.name by decide +kernel) 0
  · apply storage.status.framed
    simpa only [Address.index_zero] using PublicRHS.member_preserved frame
      (show statusName ≠ squareVar.name by decide +kernel) 0

def clocked (heap : Heap) (base : Address) : Heap :=
  replace heap (base.member clockName) ⟨.float64, true, some (.finite Binary64.one)⟩

theorem clock_store {heap : Heap} {base : Address}
    (writable : ScalarWritable heap (base.member clockName) .float64) :
    store heap (base.member clockName) (.finite Binary64.one) = some (clocked heap base) := by
  obtain ⟨old, found⟩ := writable
  exact store_float64 heap (base.member clockName) old _ found

theorem clock_reads : load (clocked heap base) (base.member clockName) =
    some (.finite Binary64.one) := by
  simp [clocked, load, convert, Value.finite]

theorem clock_frame {heap : Heap} {base : Address} {name : String}
    (different : name ≠ clockName) (i : Nat) :
    clocked heap base ((base.member name).index i) = heap ((base.member name).index i) := by
  apply replace_other
  simpa only [Address.index_zero] using Address.fields_separate base name clockName different i 0

theorem after_clock (storage : AllocatedStorage objects heap base) :
    AllocatedStorage objects (clocked heap base) base := by
  refine ⟨storage.object, storage.input.preserved (store_types (clock_store storage.clock)), ?_, ?_, ?_, ?_⟩
  · exact writable_framed storage.square (clock_frame (by decide +kernel))
  · exact writable_framed storage.jacobian (clock_frame (by decide +kernel))
  · exact ⟨some (.finite Binary64.one), replace_at _ _ _⟩
  · apply storage.status.framed
    simpa only [Address.index_zero] using
      (clock_frame (heap := heap) (base := base) (name := statusName) (by decide +kernel) 0)

/-- Exact finite bit-pattern observations, not only real-number equality. -/
structure StartupOutcome (objects : Objects) (before after : Heap) (base : Address) : Prop where
  storage : AllocatedStorage objects after base
  square : Reads after (base.member squareVar.name) (Tensor.Value.fill squareShape Binary64.positiveZero)
  status : load after (base.member statusName) = some (.integer 0)
  clock : load after (base.member clockName) = some (.finite Binary64.one)
  input : ∀ i, after ((base.member inputVar.name).index i) = before ((base.member inputVar.name).index i)
  jacobian : ∀ i, after ((base.member jacobianVar.name).index i) = before ((base.member jacobianVar.name).index i)
  frame : ∀ q, q ≠ base.member statusName → q ≠ base.member clockName →
    (∀ i < squareShape.volume, q ≠ (base.member squareVar.name).index i) → after q = before q

structure RecalibrateOutcome (objects : Objects) (before after : Heap) (base : Address) : Prop where
  storage : AllocatedStorage objects after base
  exactHeap : after = cleared before base
  status : load after (base.member statusName) = some (.integer 0)
  input : ∀ i, after ((base.member inputVar.name).index i) = before ((base.member inputVar.name).index i)
  square : ∀ i, after ((base.member squareVar.name).index i) = before ((base.member squareVar.name).index i)
  jacobian : ∀ i, after ((base.member jacobianVar.name).index i) = before ((base.member jacobianVar.name).index i)
  clock : after (base.member clockName) = before (base.member clockName)
  frame : ∀ q, q ≠ base.member statusName → after q = before q

theorem return_zero (p : CCalls.Program) (objects : Objects) (heap : Heap) (base : Address)
    (storage : AllocatedStorage objects heap base) (env : CBody.Locals) (types : CLoops.Types)
    (bound : env "self" = some (.pointer (some base)))
    (status : load heap (base.member statusName) = some (.integer 0))
    (stack : CCalls.Typed.Continuation) :
    letI : CInterface := NumericalInterface.interface
    Transition.Reaches (machine (expressions objects) p).step
      (.body (.running [.ret (some (selfField statusName))] env types heap) statusAlias stack)
      (.returning (.integer 0) heap stack) := by
  letI : CInterface := NumericalInterface.interface
  have evaluated : (expressions objects).value env heap (selfField statusName) = some (.integer 0) := by
    change CDeclaredMembers.eval TensorArrayMembers.declarations objects env heap _ = _
    rw [TensorArrayMembers.status_scalar storage.represents bound,
      TensorNumericalLinkage.selfField_eval env heap base statusName bound, status]
  have typed : typedEval (expressions objects) env types heap (selfField statusName) =
      some (.integer 0) := evaluated
  have ret : next (expressions objects) p
      (.body (.running [.ret (some (selfField statusName))] env types heap) statusAlias stack) =
      some (.body (.returned ⟨.integer 0, heap⟩) statusAlias stack) := by
    simp only [next, CCalls.Typed.nextIn, CCalls.Typed.nextWithExpressions, CLoops.nextWith, typed, bind, Option.bind_some, pure]
  exact .next ret (.next rfl (.refl _))

def initialArgs : List Expr := [selfField squareVar.name, .nat squareVar.volume]
def afterInitial : List Stmt :=
  [.assign (selfField clockName) (.cast "double" (.nat 1)), .ret (some (selfField statusName))]

theorem initial_arguments (objects : Objects) (heap : Heap) (base : Address)
    (storage : AllocatedStorage objects heap base) (env : CBody.Locals)
    (bound : env "self" = some (.pointer (some base))) :
    letI : CInterface := NumericalInterface.interface
    arguments (expressions objects) env heap initialArgs =
      some [.pointer (some (base.member squareVar.name)), .integer squareVar.volume] := by
  letI : CInterface := NumericalInterface.interface
  have output := (TensorArrayMembers.array_argument storage.represents squareVar (by simp [modelVars]) bound).1
  simp only [initialArgs, arguments, CCalls.argumentsWith, expressions, declared,
    CBody.declaredExpressions, output, CBody.evalWith,
    bind, Option.bind_some, pure]

theorem clock_step (p : CCalls.Program) (objects : Objects) (heap : Heap) (base : Address)
    (storage : AllocatedStorage objects heap base) (env : CBody.Locals) (types : CLoops.Types)
    (bound : env "self" = some (.pointer (some base))) (stack : CCalls.Typed.Continuation) :
    letI : CInterface := NumericalInterface.interface
    next (expressions objects) p (.body (.running afterInitial env types heap) statusAlias stack) =
      some (.body (.running [.ret (some (selfField statusName))] env types (clocked heap base)) statusAlias stack) := by
  letI : CInterface := NumericalInterface.interface
  have value : typedEval (expressions objects) env types heap (.cast "double" (.nat 1)) =
      some (.finite Binary64.one) := by rfl
  have address : (expressions objects).address env heap (selfField clockName) = some (base.member clockName) := by
    simp [expressions, declared, CBody.declaredExpressions, selfField, CBody.lvalueWith, CBody.evalWith,
      CBody.resolve, bound, Value.address]
  simp only [selfField] at address
  simp only [next, CCalls.Typed.nextIn, CCalls.Typed.nextWithExpressions, afterInitial, selfField, CLoops.nextWith, value, address, clock_store storage.clock,
    bind, Option.bind_some, pure]

/-- Ordinary call result on the SAME actual ten-tree table and declared
expression context; arbitrary saved callers stop at return-to-caller. -/
def MethodResult (unusedKernel : CSyntax.Program) (objects : Objects)
    (name : String) (heap finalHeap : Heap) (base : Address) : Prop :=
  letI : CInterface := NumericalInterface.interface
  (∀ stack, Transition.Reaches (machine (expressions objects) (program unusedKernel)).step
    (.calling name [.pointer (some base)] heap stack)
    (.returning (.integer 0) finalHeap stack)) ∧
  ∀ behavior, (machine (expressions objects) (program unusedKernel)).Behaves
    (.calling name [.pointer (some base)] heap .done) behavior ↔
    behavior = .terminates ⟨.integer 0, finalHeap⟩

theorem complete (unusedKernel : CSyntax.Program) (objects : Objects) (name : String)
    (code : List Stmt) (member : method name code ∈ TensorProduction.functions)
    (heap finalHeap : Heap) (base : Address)
    (ran : letI : CInterface := NumericalInterface.interface
      Transition.Reaches (machine (expressions objects) (program unusedKernel)).step
        (.body (.running (method name code).body (ContextMethod.locals base) ContextMethod.types heap)
          statusAlias .done)
        (.returning (.integer 0) finalHeap .done)) :
    MethodResult unusedKernel objects name heap finalHeap base := by
  letI : CInterface := NumericalInterface.interface
  have entered := ContextMethod.entry unusedKernel objects name code member heap base .done
  have finished : Transition.Reaches (machine (expressions objects) (program unusedKernel)).step
      (.calling name [.pointer (some base)] heap .done) (.halted ⟨.integer 0, finalHeap⟩) :=
    .next entered (ran.trans (.next rfl (.refl _)))
  exact ⟨fun stack => append_reaches (expressions objects) (program unusedKernel) finished stack,
    fun _ => (machine (expressions objects) (program unusedKernel)).behavior_iff finished rfl⟩

theorem recalibrate (unusedKernel : CSyntax.Program) (objects : Objects) (heap : Heap)
    (base : Address) (storage : AllocatedStorage objects heap base) :
    RecalibrateOutcome objects heap (cleared heap base) base ∧
      MethodResult unusedKernel objects recalibrateName heap (cleared heap base) base := by
  letI : CInterface := NumericalInterface.interface
  have outcome : RecalibrateOutcome objects heap (cleared heap base) base :=
    ⟨storage.after_clear, rfl, cleared_status_reads,
      storage.input_frame,
      storage.clear_member squareVar.name (by decide +kernel),
      storage.clear_member jacobianVar.name (by decide +kernel),
      storage.clock_frame.1, fun _ separate => cleared_other separate⟩
  refine ⟨outcome, complete unusedKernel objects recalibrateName [] ?_ heap (cleared heap base) base ?_⟩
  · simp [TensorProduction.functions, recalibrateFunction]
  · have first := method_clear recalibrateName [] objects (ContextMethod.locals base) ContextMethod.types
      heap (cleared heap base) base rfl storage.clear_store
    have step : next (expressions objects) (program unusedKernel)
        (.body (.running (method recalibrateName []).body (ContextMethod.locals base) ContextMethod.types heap)
          statusAlias .done) =
        some (.body (.running [.ret (some (selfField statusName))]
          (ContextMethod.locals base) ContextMethod.types (cleared heap base)) statusAlias .done) := by
      simp only [next, CCalls.Typed.nextIn, CCalls.Typed.nextWithExpressions, first, List.nil_append]
    exact .next step (return_zero (program unusedKernel) objects (cleared heap base) base
      storage.after_clear (ContextMethod.locals base) ContextMethod.types rfl cleared_status_reads .done)

theorem startup (unusedKernel : CSyntax.Program) (objects : Objects) (heap : Heap)
    (base : Address) (storage : AllocatedStorage objects heap base) :
    ∃ finalHeap, StartupOutcome objects heap finalHeap base ∧
      MethodResult unusedKernel objects startupName heap finalHeap base := by
  letI : CInterface := NumericalInterface.interface
  obtain ⟨initialHeap, initialReads, initialWrites, initialFrame, initialRan⟩ :=
    ContextIVP.initial TensorArrayMembers.declarations objects unusedKernel (cleared heap base)
      (fun _ => base.member squareVar.name) squareShape (by decide +kernel) storage.after_clear.square
  change Reads initialHeap (base.member squareVar.name)
    (Tensor.Value.fill squareShape Binary64.positiveZero) at initialReads
  change CallResult (expressions objects) (program unusedKernel) "rumoca_initialize"
    [.pointer (some (base.member squareVar.name)), .integer squareVar.volume]
    (cleared heap base) initialHeap at initialRan
  have initialStorage := after_initial storage.after_clear initialWrites initialFrame
  let finalHeap := clocked initialHeap base
  have finalStorage : AllocatedStorage objects finalHeap base := after_clock initialStorage
  have finalSquare : Reads finalHeap (base.member squareVar.name)
      (Tensor.Value.fill squareShape Binary64.positiveZero) :=
    reads_framed initialReads (clock_frame (by decide +kernel))
  have initialStatus : initialHeap (base.member statusName) = (cleared heap base) (base.member statusName) := by
    simpa only [Address.index_zero] using PublicRHS.member_preserved initialFrame
      (show statusName ≠ squareVar.name by decide +kernel) 0
  have finalStatusCell : finalHeap (base.member statusName) = initialHeap (base.member statusName) := by
    simpa only [Address.index_zero] using
      (clock_frame (heap := initialHeap) (base := base) (name := statusName) (by decide +kernel) 0)
  have finalStatus : load finalHeap (base.member statusName) = some (.integer 0) := by
    simpa only [load, finalStatusCell, initialStatus] using
      (cleared_status_reads (heap := heap) (base := base))
  have inputFrame : ∀ i, finalHeap ((base.member inputVar.name).index i) =
      heap ((base.member inputVar.name).index i) := fun i =>
    (clock_frame (by decide +kernel) i).trans
      ((PublicRHS.member_preserved initialFrame (show inputVar.name ≠ squareVar.name by decide +kernel) i).trans
        (storage.input_frame i))
  have jacFrame : ∀ i, finalHeap ((base.member jacobianVar.name).index i) =
      heap ((base.member jacobianVar.name).index i) := fun i =>
    (clock_frame (by decide +kernel) i).trans
      ((PublicRHS.member_preserved initialFrame (show jacobianVar.name ≠ squareVar.name by decide +kernel) i).trans
        (storage.clear_member jacobianVar.name (by decide +kernel) i))
  have outcome : StartupOutcome objects heap finalHeap base :=
    ⟨finalStorage, finalSquare, finalStatus, clock_reads, inputFrame, jacFrame,
      fun q status clock outside =>
        (replace_other _ _ _ _ clock).trans ((initialFrame q outside).trans (cleared_other status))⟩
  refine ⟨finalHeap, outcome, complete unusedKernel objects startupName
    [.eval (.call (.id "rumoca_initialize") initialArgs),
      .assign (selfField clockName) (.cast "double" (.nat 1))] ?_ heap finalHeap base ?_⟩
  · simp [TensorProduction.functions, startupFunction, initialArgs]
  · have first := method_clear startupName
      [.eval (.call (.id "rumoca_initialize") initialArgs),
        .assign (selfField clockName) (.cast "double" (.nat 1))]
      objects (ContextMethod.locals base) ContextMethod.types heap (cleared heap base) base rfl storage.clear_store
    have step : next (expressions objects) (program unusedKernel)
        (.body (.running (method startupName
          [.eval (.call (.id "rumoca_initialize") initialArgs),
            .assign (selfField clockName) (.cast "double" (.nat 1))]).body
          (ContextMethod.locals base) ContextMethod.types heap) statusAlias .done) =
        some (.body (.running (.eval (.call (.id "rumoca_initialize") initialArgs) :: afterInitial)
          (ContextMethod.locals base) ContextMethod.types (cleared heap base)) statusAlias .done) := by
      simp only [next, CCalls.Typed.nextIn, CCalls.Typed.nextWithExpressions, first]
      rfl
    have initialDone := invoke_reaches (expressions objects) (program unusedKernel) initialRan initialArgs
      afterInitial (ContextMethod.locals base) ContextMethod.types statusAlias .done (by decide +kernel)
      (by rfl) (by rfl)
      (initial_arguments objects (cleared heap base) base storage.after_clear (ContextMethod.locals base) rfl)
    exact .next step (initialDone.trans
      (.next (clock_step (program unusedKernel) objects initialHeap base initialStorage
        (ContextMethod.locals base) ContextMethod.types rfl .done)
        (return_zero (program unusedKernel) objects finalHeap base finalStorage
          (ContextMethod.locals base) ContextMethod.types rfl finalStatus .done)))


end Rumoca.EFMI.AllocatedMethods
