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
      (show GALEC.Names.clock ≠ squareVar.name by decide +kernel) 0
  · apply storage.status.framed
    simpa only [Address.index_zero] using PublicRHS.member_preserved frame
      (show statusName ≠ squareVar.name by decide +kernel) 0

def clocked (heap : Heap) (base : Address) : Heap :=
  replace heap (base.member GALEC.Names.clock) ⟨.float64, true, some (.finite Binary64.one)⟩

theorem clock_store {heap : Heap} {base : Address}
    (writable : ScalarWritable heap (base.member GALEC.Names.clock) .float64) :
    store heap (base.member GALEC.Names.clock) (.finite Binary64.one) = some (clocked heap base) := by
  obtain ⟨old, found⟩ := writable
  exact store_float64 heap (base.member GALEC.Names.clock) old _ found

theorem clock_reads : load (clocked heap base) (base.member GALEC.Names.clock) =
    some (.finite Binary64.one) := by
  simp [clocked, load, convert, Value.finite]

theorem clock_frame {heap : Heap} {base : Address} {name : String}
    (different : name ≠ GALEC.Names.clock) (i : Nat) :
    clocked heap base ((base.member name).index i) = heap ((base.member name).index i) := by
  apply replace_other
  simpa only [Address.index_zero] using Address.fields_separate base name GALEC.Names.clock different i 0

theorem after_clock (storage : AllocatedStorage objects heap base) :
    AllocatedStorage objects (clocked heap base) base := by
  refine ⟨storage.object, storage.input.preserved (store_types (clock_store storage.clock)), ?_, ?_, ?_, ?_⟩
  · exact writable_framed storage.square (clock_frame (by decide +kernel))
  · exact writable_framed storage.jacobian (clock_frame (by decide +kernel))
  · exact ⟨some (.finite Binary64.one), replace_at _ _ _⟩
  · apply storage.status.framed
    simpa only [Address.index_zero] using
      (clock_frame (heap := heap) (base := base) (name := statusName) (by decide +kernel) 0)

structure RecalibrateOutcome (objects : Objects) (before after : Heap) (base : Address) : Prop where
  storage : AllocatedStorage objects after base
  exactHeap : after = cleared before base
  status : load after (base.member statusName) = some (.integer 0)
  input : ∀ i, after ((base.member inputVar.name).index i) = before ((base.member inputVar.name).index i)
  square : ∀ i, after ((base.member squareVar.name).index i) = before ((base.member squareVar.name).index i)
  jacobian : ∀ i, after ((base.member jacobianVar.name).index i) = before ((base.member jacobianVar.name).index i)
  clock : after (base.member GALEC.Names.clock) = before (base.member GALEC.Names.clock)
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

/-- The Startup body after both initializer calls. -/
def afterInitialization : List Stmt :=
  [.assign (selfField GALEC.Names.clock) (.cast "double" (.nat 1)), .ret (some (selfField statusName))]

theorem initial_arguments (objects : Objects) (heap : Heap) (base : Address)
    (storage : AllocatedStorage objects heap base) (env : CBody.Locals)
    (bound : env "self" = some (.pointer (some base))) :
    letI : CInterface := NumericalInterface.interface
    arguments (expressions objects) env heap squareInitializerArgs =
      some [.pointer (some (base.member squareVar.name)), .integer squareVar.volume] := by
  letI : CInterface := NumericalInterface.interface
  have output := (TensorArrayMembers.array_argument storage.represents squareVar (by simp [modelVars]) bound).1
  simp only [squareInitializerArgs, arguments, CCalls.argumentsWith, expressions, declared,
    CBody.declaredExpressions, output, CBody.evalWith,
    bind, Option.bind_some, pure]

theorem clock_step (p : CCalls.Program) (objects : Objects) (heap : Heap) (base : Address)
    (storage : AllocatedStorage objects heap base) (env : CBody.Locals) (types : CLoops.Types)
    (bound : env "self" = some (.pointer (some base))) (stack : CCalls.Typed.Continuation) :
    letI : CInterface := NumericalInterface.interface
    next (expressions objects) p (.body (.running afterInitialization env types heap) statusAlias stack) =
      some (.body (.running [.ret (some (selfField statusName))] env types (clocked heap base)) statusAlias stack) := by
  letI : CInterface := NumericalInterface.interface
  have value : typedEval (expressions objects) env types heap (.cast "double" (.nat 1)) =
      some (.finite Binary64.one) := by rfl
  have address : (expressions objects).address env heap (selfField GALEC.Names.clock) = some (base.member GALEC.Names.clock) := by
    simp [expressions, declared, CBody.declaredExpressions, selfField, CBody.lvalueWith, CBody.evalWith,
      CBody.resolve, bound, Value.address]
  simp only [selfField] at address
  simp only [next, CCalls.Typed.nextIn, CCalls.Typed.nextWithExpressions, afterInitialization, selfField, CLoops.nextWith, value, address, clock_store storage.clock,
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
  exact ContextMethod.complete_in (program unusedKernel) objects name code
    (method_defined unusedKernel (method name code) member) heap finalHeap base ran

/-- The unchanged Recalibrate body requires no function-table extension or
input-value interpretation; it preserves the supplied locals and continuation. -/
theorem recalibrate_body_in (p : CCalls.Program) (objects : Objects) (heap : Heap)
    (base : Address) (storage : AllocatedStorage objects heap base)
    (env : CBody.Locals) (types : CLoops.Types)
    (bound : env "self" = some (.pointer (some base)))
    (stack : CCalls.Typed.Continuation) :
    letI : CInterface := NumericalInterface.interface
    Transition.Reaches (machine (expressions objects) p).step
      (.body (.running recalibrateFunction.body env types heap) statusAlias stack)
      (.returning (.integer 0) (cleared heap base) stack) := by
  letI : CInterface := NumericalInterface.interface
  have first := method_clear recalibrateName [] objects env types
    heap (cleared heap base) base bound storage.clear_store
  have step : next (expressions objects) p
      (.body (.running (method recalibrateName []).body env types heap) statusAlias stack) =
      some (.body (.running [.ret (some (selfField statusName))]
        env types (cleared heap base)) statusAlias stack) := by
    simp only [next, CCalls.Typed.nextIn, CCalls.Typed.nextWithExpressions, first, List.nil_append]
  exact .next step (return_zero p objects (cleared heap base) base
    storage.after_clear env types bound cleared_status_reads stack)

/-- Exact lookup of the unchanged Recalibrate definition suffices for its full
owned outcome and ordinary public behavior on the supplied table. -/
theorem recalibrate_in (p : CCalls.Program) (objects : Objects) (heap : Heap)
    (base : Address) (storage : AllocatedStorage objects heap base)
    (found : p.definitions recalibrateName = some (.tree recalibrateFunction)) :
    RecalibrateOutcome objects heap (cleared heap base) base ∧
      ContextMethod.Completes p objects recalibrateName heap (cleared heap base) base := by
  have outcome : RecalibrateOutcome objects heap (cleared heap base) base :=
    ⟨storage.after_clear, rfl, cleared_status_reads,
      storage.input_frame,
      storage.clear_member squareVar.name (by decide +kernel),
      storage.clear_member jacobianVar.name (by decide +kernel),
      storage.clock_frame.1, fun _ separate => cleared_other separate⟩
  exact ⟨outcome, ContextMethod.complete_in p objects recalibrateName [] found
    heap (cleared heap base) base
    (recalibrate_body_in p objects heap base storage (ContextMethod.locals base) ContextMethod.types rfl .done)⟩

theorem recalibrate (unusedKernel : CSyntax.Program) (objects : Objects) (heap : Heap)
    (base : Address) (storage : AllocatedStorage objects heap base) :
    RecalibrateOutcome objects heap (cleared heap base) base ∧
      MethodResult unusedKernel objects recalibrateName heap (cleared heap base) base := by
  exact recalibrate_in (program unusedKernel) objects heap base storage
    (method_defined unusedKernel recalibrateFunction (by simp [TensorProduction.functions]))

theorem after_jacobian (storage : AllocatedStorage objects heap base)
    (writes : Writable after (base.member jacobianVar.name) jacobianShape.volume)
    (frame : ∀ q, (∀ i < jacobianShape.volume, q ≠ (base.member jacobianVar.name).index i) →
      after q = heap q) : AllocatedStorage objects after base := by
  refine ⟨storage.object, ?_, ?_, writes, ?_, ?_⟩
  · exact allocated_frame storage.input (PublicRHS.member_preserved frame (by decide +kernel))
  · exact writable_framed storage.square (PublicRHS.member_preserved frame (by decide +kernel))
  · apply storage.clock.framed
    simpa only [Address.index_zero] using PublicRHS.member_preserved frame
      (show GALEC.Names.clock ≠ jacobianVar.name by decide +kernel) 0
  · apply storage.status.framed
    simpa only [Address.index_zero] using PublicRHS.member_preserved frame
      (show statusName ≠ jacobianVar.name by decide +kernel) 0

theorem jacobian_arguments (objects : Objects) (heap : Heap) (base : Address)
    (storage : AllocatedStorage objects heap base) (env : CBody.Locals)
    (bound : env "self" = some (.pointer (some base))) :
    letI : CInterface := NumericalInterface.interface
    arguments (expressions objects) env heap jacobianInitializerArgs =
      some [.pointer (some (base.member jacobianVar.name)), .integer jacobianVar.volume] := by
  letI : CInterface := NumericalInterface.interface
  have output := (TensorArrayMembers.array_argument storage.represents jacobianVar
    (by simp [modelVars]) bound).1
  simp only [jacobianInitializerArgs, arguments, CCalls.argumentsWith, expressions, declared,
    CBody.declaredExpressions, output, CBody.evalWith, bind, Option.bind_some, pure]

structure InitializationOutcome (objects : Objects) (before after : Heap) (base : Address) : Prop where
  storage : AllocatedStorage objects after base
  square : Reads after (base.member squareVar.name)
    (Tensor.Value.fill squareShape Binary64.positiveZero)
  jacobian : Reads after (base.member jacobianVar.name)
    (Tensor.Value.fill jacobianShape Binary64.positiveZero)
  input : ∀ i, after ((base.member inputVar.name).index i) = before ((base.member inputVar.name).index i)
  frame : ∀ q,
    (∀ i < squareShape.volume, q ≠ (base.member squareVar.name).index i) →
    (∀ i < jacobianShape.volume, q ≠ (base.member jacobianVar.name).index i) →
    after q = before q

theorem InitializationOutcome.member_frame (h : InitializationOutcome objects before after base)
    (name : String) (notSquare : name ≠ squareVar.name) (notJacobian : name ≠ jacobianVar.name)
    (i : Nat) : after ((base.member name).index i) = before ((base.member name).index i) :=
  h.frame _ (fun j _ => Address.fields_separate base name squareVar.name notSquare i j)
    (fun j _ => Address.fields_separate base name jacobianVar.name notJacobian i j)

/-- The initializer calls for `x` and `J` execute under the actual numerical
table. They require neither finite prior values nor an initialized input. The arbitrary
tail is restored with unchanged caller locals, types, return type and stack. -/
theorem initialization_executes (unusedKernel : CSyntax.Program) (objects : Objects) (heap : Heap)
    (base : Address) (storage : AllocatedStorage objects heap base)
    (env : CBody.Locals) (types : CLoops.Types) (resultType : String)
    (bound : env "self" = some (.pointer (some base)))
    (unshadowed : env "rumoca_initialize" = none)
    (tail : List Stmt) (stack : CCalls.Typed.Continuation) :
    letI : CInterface := NumericalInterface.interface
    ∃ after, InitializationOutcome objects heap after base ∧
      Transition.Reaches (machine (expressions objects) (program unusedKernel)).step
        (.body (.running (initializationPrefix ++ tail) env types heap) resultType stack)
        (.body (.running tail env types after) resultType stack) := by
  letI : CInterface := NumericalInterface.interface
  obtain ⟨xHeap, xReads, xWrites, xFrame, xRan⟩ :=
    ContextIVP.initial TensorArrayMembers.declarations objects unusedKernel heap
      (fun _ => base.member squareVar.name) squareShape (by decide +kernel) storage.square
  change Reads xHeap (base.member squareVar.name)
    (Tensor.Value.fill squareShape Binary64.positiveZero) at xReads
  change CallResult (expressions objects) (program unusedKernel) "rumoca_initialize"
    [.pointer (some (base.member squareVar.name)), .integer squareVar.volume] heap xHeap at xRan
  have xStorage := after_initial storage xWrites xFrame
  obtain ⟨jHeap, jReads, jWrites, jFrame, jRan⟩ :=
    ContextIVP.initial TensorArrayMembers.declarations objects unusedKernel xHeap
      (fun _ => base.member jacobianVar.name) jacobianShape (by decide +kernel) xStorage.jacobian
  change Reads jHeap (base.member jacobianVar.name)
    (Tensor.Value.fill jacobianShape Binary64.positiveZero) at jReads
  change CallResult (expressions objects) (program unusedKernel) "rumoca_initialize"
    [.pointer (some (base.member jacobianVar.name)), .integer jacobianVar.volume] xHeap jHeap at jRan
  have jStorage := after_jacobian xStorage jWrites jFrame
  have finalSquare := reads_framed xReads
    (PublicRHS.member_preserved jFrame (show squareVar.name ≠ jacobianVar.name by decide +kernel))
  have outcome : InitializationOutcome objects heap jHeap base :=
    ⟨jStorage, finalSquare, jReads,
      fun i => (PublicRHS.member_preserved jFrame
        (show inputVar.name ≠ jacobianVar.name by decide +kernel) i).trans
        (PublicRHS.member_preserved xFrame (show inputVar.name ≠ squareVar.name by decide +kernel) i),
      fun q outsideX outsideJ => (jFrame q outsideJ).trans (xFrame q outsideX)⟩
  have first := invoke_reaches (expressions objects) (program unusedKernel) xRan squareInitializerArgs
    (.eval (.call (.id "rumoca_initialize") jacobianInitializerArgs) :: tail) env types resultType stack
    (by decide +kernel) unshadowed (by rfl)
    (initial_arguments objects heap base storage env bound)
  have second := invoke_reaches (expressions objects) (program unusedKernel) jRan jacobianInitializerArgs
    tail env types resultType stack (by decide +kernel) unshadowed (by rfl)
    (jacobian_arguments objects xHeap base xStorage env bound)
  exact ⟨jHeap, outcome, first.trans second⟩

/-- The emitted Startup method is the initialization prefix followed by the
sample-period assignment. -/
theorem startup_method : startupFunction =
    method startupName
      (initializationPrefix ++ [.assign (selfField GALEC.Names.clock) (.cast "double" (.nat 1))]) :=
  rfl

/-- Exact finite bit-pattern observations, not only real-number equality: both
outputs read positive zero, the period is one and the status is zero. Only the
two output buffers and the two scalar fields may change. -/
structure StartupOutcome (objects : Objects) (before after : Heap) (base : Address) : Prop where
  storage : AllocatedStorage objects after base
  square : Reads after (base.member squareVar.name)
    (Tensor.Value.fill squareShape Binary64.positiveZero)
  jacobian : Reads after (base.member jacobianVar.name)
    (Tensor.Value.fill jacobianShape Binary64.positiveZero)
  status : load after (base.member statusName) = some (.integer 0)
  clock : load after (base.member GALEC.Names.clock) = some (.finite Binary64.one)
  input : ∀ i, after ((base.member inputVar.name).index i) = before ((base.member inputVar.name).index i)
  frame : ∀ q, q ≠ base.member statusName → q ≠ base.member GALEC.Names.clock →
    (∀ i < squareShape.volume, q ≠ (base.member squareVar.name).index i) →
    (∀ i < jacobianShape.volume, q ≠ (base.member jacobianVar.name).index i) →
    after q = before q

/-- The emitted Startup body returns status zero to any saved caller. Input
storage is allocated only; old output, status and clock contents are arbitrary. -/
theorem startup_body (unusedKernel : CSyntax.Program) (objects : Objects) (heap : Heap)
    (base : Address) (storage : AllocatedStorage objects heap base)
    (env : CBody.Locals) (types : CLoops.Types)
    (bound : env "self" = some (.pointer (some base)))
    (unshadowed : env "rumoca_initialize" = none)
    (stack : CCalls.Typed.Continuation) :
    letI : CInterface := NumericalInterface.interface
    ∃ after, StartupOutcome objects heap after base ∧
      Transition.Reaches (machine (expressions objects) (program unusedKernel)).step
        (.body (.running startupFunction.body env types heap) statusAlias stack)
        (.returning (.integer 0) after stack) := by
  letI : CInterface := NumericalInterface.interface
  obtain ⟨initialized, outcome, initializedRan⟩ := initialization_executes unusedKernel objects
    (cleared heap base) base storage.after_clear env types statusAlias bound unshadowed
    afterInitialization stack
  let finalHeap := clocked initialized base
  have finalStorage : AllocatedStorage objects finalHeap base := after_clock outcome.storage
  have finalSquare : Reads finalHeap (base.member squareVar.name)
      (Tensor.Value.fill squareShape Binary64.positiveZero) :=
    reads_framed outcome.square (clock_frame (by decide +kernel))
  have finalJacobian : Reads finalHeap (base.member jacobianVar.name)
      (Tensor.Value.fill jacobianShape Binary64.positiveZero) :=
    reads_framed outcome.jacobian (clock_frame (by decide +kernel))
  have initializedStatus : initialized (base.member statusName) =
      (cleared heap base) (base.member statusName) := by
    simpa only [Address.index_zero] using
      outcome.member_frame statusName (by decide +kernel) (by decide +kernel) 0
  have finalStatusCell : finalHeap (base.member statusName) = initialized (base.member statusName) := by
    simpa only [Address.index_zero] using
      (clock_frame (heap := initialized) (base := base) (name := statusName) (by decide +kernel) 0)
  have finalStatus : load finalHeap (base.member statusName) = some (.integer 0) := by
    simpa only [load, finalStatusCell, initializedStatus] using
      (cleared_status_reads (heap := heap) (base := base))
  have finalOutcome : StartupOutcome objects heap finalHeap base :=
    ⟨finalStorage, finalSquare, finalJacobian, finalStatus, clock_reads,
      fun i => (clock_frame (by decide +kernel) i).trans
        ((outcome.input i).trans (storage.input_frame i)),
      fun q status clock outsideX outsideJ => (replace_other _ _ _ _ clock).trans
        ((outcome.frame q outsideX outsideJ).trans (cleared_other status))⟩
  have first := method_clear startupName
    (initializationPrefix ++ [.assign (selfField GALEC.Names.clock) (.cast "double" (.nat 1))])
    objects env types heap (cleared heap base) base bound storage.clear_store
  have start : next (expressions objects) (program unusedKernel)
      (.body (.running startupFunction.body env types heap) statusAlias stack) =
      some (.body (.running (initializationPrefix ++ afterInitialization) env types (cleared heap base))
        statusAlias stack) := by
    simp only [startup_method, next, CCalls.Typed.nextIn, CCalls.Typed.nextWithExpressions, first]
    rfl
  exact ⟨finalHeap, finalOutcome, .next start (initializedRan.trans
    (.next (clock_step (program unusedKernel) objects initialized base outcome.storage
      env types bound stack)
      (return_zero (program unusedKernel) objects finalHeap base finalStorage
        env types bound finalStatus stack)))⟩

theorem startup (unusedKernel : CSyntax.Program) (objects : Objects) (heap : Heap)
    (base : Address) (storage : AllocatedStorage objects heap base) :
    ∃ finalHeap, StartupOutcome objects heap finalHeap base ∧
      MethodResult unusedKernel objects startupName heap finalHeap base := by
  obtain ⟨finalHeap, outcome, ran⟩ := startup_body unusedKernel objects heap base storage
    (ContextMethod.locals base) ContextMethod.types rfl rfl .done
  rw [startup_method] at ran
  have member : startupFunction ∈ TensorProduction.functions := by
    simp [TensorProduction.functions]
  rw [startup_method] at member
  exact ⟨finalHeap, outcome, complete unusedKernel objects startupName _ member
    heap finalHeap base ran⟩

end Rumoca.EFMI.AllocatedMethods
