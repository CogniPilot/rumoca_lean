import RumocaFMI3.ReservationOriginRuntime

namespace Rumoca.FMI3.ReservationOrigin
open CTree CMemory CCalls CCallSites

/-- The actual factory suffix contains no second reservation, in either the
exhaustion branch or instance initialization. -/
theorem factory_suffix_closed (model : Solve.Model source) (kind : Kind) :
    ∀ stmt ∈ StaticFactory.guard :: StaticFactory.initializeInstance model kind, Admits Permitted stmt := by
  check_no_reservation

/-- On return from the helper, the saved factory suffix itself supplies the
closed call-domain invariant. No successful allocation outcome is assumed. -/
theorem factory_return_closed (model : Solve.Model source) (kind : Kind)
    (value : Value) (heap : Heap) (env : CBody.Locals) (types : CLoops.Types) :
    Ready Permitted (fun name _ => allowed name = true)
      (.returning value heap
        (.caller (.declare "size_t" "slot")
          (StaticFactory.guard :: StaticFactory.initializeInstance model kind) env types "fmi3Instance" .done)) :=
  ⟨factory_suffix_closed model kind, True.intro⟩

variable [interface : CInterface] {E : Type}

/-- The remainder of a real factory call cannot reenter a factory, its scan,
or atomic exchange. Other threads retain their independent controls and may
continue reserving. This claim is about the selected invocation only. -/
theorem factory_suffix_history (model : Solve.FMI3Model source) (sigs : List Signature)
    (program : Events.Program E) (actual : program.internal = LiteralPreparation.program model sigs)
    (onlyNamed : ∀ name, allowed name = false → NamedOnly program name)
    (kind : Kind) (value : Value) (heap : Heap) (env : CBody.Locals) (types : CLoops.Types)
    (entry : before.threads tracked = some (.returning value heap
      (.caller (.declare "size_t" "slot")
        (StaticFactory.guard :: StaticFactory.initializeInstance model.solve kind) env types "fmi3Instance" .done)))
    (path : Transition.Reaches (fun a b => ∃ thread effects, Concurrent.Step program a thread effects b) before after) :
    ∀ name args savedHeap stack, after.threads tracked = some (.calling name args savedHeap stack) → allowed name = true := by
  have start : ∃ saved, before.threads tracked = some saved ∧
      Ready Permitted (fun name _ => allowed name = true) saved :=
    ⟨_, entry, factory_return_closed model.solve kind value heap env types⟩
  have finish : ∃ saved, after.threads tracked = some saved ∧
      Ready Permitted (fun name _ => allowed name = true) saved := by
    clear entry
    induction path with
    | refl => exact start
    | next first rest ih =>
      obtain ⟨thread, effects, step⟩ := first
      obtain ⟨saved, found, ready⟩ := start
      cases step with
      | run selected executed =>
        by_cases same : thread = tracked
        · subst thread
          cases Option.some.inj (selected.symm.trans found)
          have next := event_ready model sigs program actual onlyNamed
            ((ready_withHeap _ _).mpr ready) executed
          exact ih ⟨_, by simp [Concurrent.update, Concurrent.control], (ready_withHeap _ (fun _ => none)).mpr next⟩
        · exact ih ⟨saved, by simpa [Concurrent.update, Ne.symm same] using found, ready⟩
  obtain ⟨saved, found, ready⟩ := finish
  intro name args savedHeap stack calling
  cases Option.some.inj (found.symm.trans calling)
  exact ready.1

end Rumoca.FMI3.ReservationOrigin


namespace Rumoca.FMI3.ReservationOrigin
open CTree CMemory CCalls CCalls.Events CCallSites RuntimeLinkage
variable [interface : CInterface]

/-- The actual generated/library/logger environment discharges the closed
suffix's call-address boundary for every remaining shared C history. -/
theorem logged_factory_suffix (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (boolean : interface.types "_Bool" = some .boolean)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32)
    (double : interface.types "double" = some .float64)
    (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
    (logger : Address) (effect : ReturningEffect (Logging.signature hostName)) :
    let program := logged model sigs covered tag boolean size integer double observed range logger effect
    ∀ (kind : Kind) (value : Value) (heap : Heap) (env : CBody.Locals) (types : CLoops.Types)
      (before after : Concurrent.State) (tracked : Nat),
      before.threads tracked = some (.returning value heap
        (.caller (.declare "size_t" "slot")
          (StaticFactory.guard :: StaticFactory.initializeInstance model.solve kind) env types "fmi3Instance" .done)) →
      Transition.Reaches (fun a b => ∃ thread effects, Concurrent.Step program a thread effects b) before after →
      ∀ name args savedHeap stack, after.threads tracked = some (.calling name args savedHeap stack) → allowed name = true := by
  intro program kind value heap env types before after tracked entry path
  exact factory_suffix_history model sigs program rfl
    (fun _ outside => logged_named_only model sigs covered tag boolean size integer double observed range logger effect outside)
    kind value heap env types entry path

end Rumoca.FMI3.ReservationOrigin
