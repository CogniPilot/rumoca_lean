import RumocaFMI3.StaticFactoryCode
import RumocaFMI3.InstanceSlot
import RumocaC.LoopProofs

/-! Select the reserved typed array element and establish the successful
factory suffix's complete execution and postcondition. Reservation itself,
global bindings and public argument entry remain separate composition steps. -/
noncomputable section
namespace Rumoca.FMI3.StaticFactory
open CTree CMemory CBody
variable [interface : CInterface]

theorem select_step (env : Locals) (types : CLoops.Types) (heap : Heap)
    (base : Address) (slot : Nat) (rest : List Stmt)
    (instances : resolve env "rumoca_instances" = some (.pointer (some base)))
    (selected : resolve env "slot" = some (.integer slot))
    (fresh : env "m" = none) (pointer : interface.types "Instance *" = some .pointer) :
    CLoops.next (.running (selectInstance :: rest) env types heap) =
      some (.running rest (CBody.bind env "m" (.pointer (some (base.index slot))))
        (CLoops.bindType types "m" .pointer) heap) := by
  apply CLoops.declare_local env types heap "Instance *" "m" _ rest .pointer
    (.pointer (some (base.index slot))) (.pointer (some (base.index slot))) pointer fresh ?_ rfl
  have nonnegative : ¬ (slot : Int) < 0 := by omega
  simp [CLoops.eval, CLoops.evalWith, legacyExpressions, eval, evalWith, lvalueWith,
    instances, selected, Value.address, nonnegative]

theorem guard_step (env : Locals) (types : CLoops.Types) (heap : Heap)
    (slot capacity : Nat) (rest : List Stmt)
    (selected : resolve env "slot" = some (.integer slot))
    (count : resolve env "rumoca_instance_capacity" = some (.integer capacity)) :
    CLoops.next (.running (guard :: rest) env types heap) =
      some (.running ((if slot = capacity then exhausted else []) ++ rest) env types heap) := by
  by_cases same : slot = capacity
  · subst slot
    simp [guard, exhausted, FactoryRejection.code, FactoryRejection.logCall,
      CLoops.next, CLoops.nextWith, CLoops.noDeclarations, CLoops.evalWith,
      legacyExpressions, eval, evalWith,
      selected, count, comparison, boolean, Value.truth]
  · have different : (slot : Int) ≠ (capacity : Int) := by omega
    simp [guard, exhausted, FactoryRejection.code, FactoryRejection.logCall,
      CLoops.next, CLoops.nextWith, CLoops.noDeclarations, CLoops.evalWith,
      legacyExpressions, eval, evalWith,
      selected, count, comparison, boolean, Value.truth, same, different]

theorem selected_bindings (env : Locals) (p : Address) (environment logger : Option Address)
    (logging : Bool)
    (environmentBound : resolve env "instanceEnvironment" = some (.pointer environment))
    (loggerBound : resolve env "logMessage" = some (.pointer logger))
    (loggingBound : resolve env "loggingOn" = some (boolean logging)) :
    InstanceInitialization.Bindings (CBody.bind env "m" (.pointer (some p))) p environment logger logging := by
  constructor
  · simp [resolve, CBody.bind]
  · simpa [resolve, CBody.bind] using environmentBound
  · simpa [resolve, CBody.bind] using loggerBound
  · simpa [resolve, CBody.bind] using loggingBound

theorem initialization_reaches (program : CCalls.Events.Program E) (model : Solve.Model source)
    (kind : Kind) (env : Locals) (types : CLoops.Types) (heap : Heap)
    (base : Address) (capacity : Nat) (slot : Fin capacity)
    (environment logger : Option Address) (logging : Bool) (stack : CCalls.Typed.Continuation)
    (storage : InstanceSlot.Storage heap (base.index slot.val))
    (bounded : slot.val < 2^64)
    (instances : resolve env "rumoca_instances" = some (.pointer (some base)))
    (selected : resolve env "slot" = some (.integer slot.val))
    (fresh : env "m" = none)
    (environmentBound : resolve env "instanceEnvironment" = some (.pointer environment))
    (loggerBound : resolve env "logMessage" = some (.pointer logger))
    (loggingBound : resolve env "loggingOn" = some (boolean logging))
    (pointer : interface.types "Instance *" = some .pointer)
    (double : interface.types "double" = some .float64)
    (handle : interface.types "fmi3Instance" = some .pointer) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (initializeInstance model kind) env types heap) "fmi3Instance" stack)
      (.returning (.pointer (some (base.index slot.val)))
        (InstanceSlot.finalHeap heap (base.index slot.val) slot.val kind environment logger logging) stack) := by
  refine .next (CCalls.Events.body_step program
    (select_step env types heap base slot.val _ instances selected fresh pointer) "fmi3Instance" stack) ?_
  exact InstanceSlot.return_reaches program model kind _ _ heap (base.index slot.val) slot.val
    environment logger logging stack storage
    (selected_bindings env _ environment logger logging environmentBound loggerBound loggingBound)
    (by simpa [resolve, CBody.bind] using selected) bounded double handle

/-- An already in-range selection passes the exhaustion-sentinel guard and
initializes the record. Bounds come from `slot : Fin capacity`, supplied by
the scan outcome in the composed factory proof, not from the equality guard. -/
theorem guarded_initialization (program : CCalls.Events.Program E) (model : Solve.Model source)
    (kind : Kind) (env : Locals) (types : CLoops.Types) (heap : Heap)
    (base : Address) (capacity : Nat) (slot : Fin capacity)
    (environment logger : Option Address) (logging : Bool) (stack : CCalls.Typed.Continuation)
    (storage : InstanceSlot.Storage heap (base.index slot.val))
    (bounded : slot.val < 2^64)
    (instances : resolve env "rumoca_instances" = some (.pointer (some base)))
    (selected : resolve env "slot" = some (.integer slot.val))
    (count : resolve env "rumoca_instance_capacity" = some (.integer capacity))
    (fresh : env "m" = none)
    (environmentBound : resolve env "instanceEnvironment" = some (.pointer environment))
    (loggerBound : resolve env "logMessage" = some (.pointer logger))
    (loggingBound : resolve env "loggingOn" = some (boolean logging))
    (pointer : interface.types "Instance *" = some .pointer)
    (double : interface.types "double" = some .float64)
    (handle : interface.types "fmi3Instance" = some .pointer) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (guard :: initializeInstance model kind) env types heap) "fmi3Instance" stack)
      (.returning (.pointer (some (base.index slot.val)))
        (InstanceSlot.finalHeap heap (base.index slot.val) slot.val kind environment logger logging) stack) := by
  have different : slot.val ≠ capacity := Nat.ne_of_lt slot.isLt
  have first := guard_step env types heap slot.val capacity (initializeInstance model kind) selected count
  simp only [different, ↓reduceIte, List.nil_append] at first
  exact .next (CCalls.Events.body_step program first "fmi3Instance" stack)
    (initialization_reaches program model kind env types heap base capacity slot environment logger logging stack
      storage bounded instances selected fresh environmentBound loggerBound loggingBound pointer double handle)

end Rumoca.FMI3.StaticFactory
