import RumocaFMI3.Float64Access

noncomputable section
namespace Rumoca.FMI3.Float64Access
open CMemory Float64Buffers

/-- Raw bounded readback has no numerical or success condition. -/
def Request.readback (request : Request) (heap : Heap) (buffers : Layout) : Nat → Option Value :=
  match request with
  | .get shape _ => fun i => if i < shape.volume then load heap (buffers.values.index i) else none
  | .set _ => fun _ => none

def Request.expected (request : Request) (model : Solve.FMI3Model source)
    (state : ModelExchange.State) (time : Binary64.Value) : Nat → Option Value :=
  match request with
  | .get shape references => fun i => if i < shape.volume then
      some (.finite ((Float64Calls.selectReference (references i)).value model state time)) else none
  | .set _ => fun _ => none

theorem Request.readback_correct {request : Request} (observes : request.Observes model state time heap buffers) :
    request.readback heap buffers = request.expected model state time := by
  cases request with
  | get shape references =>
    funext i
    by_cases inside : i < shape.volume
    · exact (if_pos inside).trans ((observes i inside).trans (if_pos inside).symm)
    · simp only [Request.readback, Request.expected, if_neg inside]
  | set _ => rfl

def finalState : List Request → ModelExchange.State → ModelExchange.State
  | [], state => state
  | request :: rest, state => finalState rest (request.next state)

def expected (model : Solve.FMI3Model source) (time : Binary64.Value) :
    List Request → ModelExchange.State → List (Nat → Option Value)
  | [], _ => []
  | request :: rest, state => request.expected model state time :: expected model time rest (request.next state)

structure Observation (E : Type) where
  events : List E
  status : Value
  values : Nat → Option Value

def Observation.ok (values : Nat → Option Value) : Observation E := ⟨[], .integer 0, values⟩

/-- The actual script records arbitrary returned events/statuses and raw
memory readback. It does not assume the compiler's expected observations. -/
inductive Executed [CInterface] (program : CCalls.Events.Program E) (p : Address) (buffers : Layout) :
    Heap → List Request → List (Observation E) → Heap → Prop where
  | nil : Executed program p buffers heap [] [] heap
  | cons : request.hostRun heap buffers = some ready →
      (CCalls.Events.machine program).Behaves
        (.calling (request.call p buffers).1 (request.call p buffers).2 ready .done)
        (.terminates events ⟨status, after⟩) →
      request.readback after buffers = values →
      Executed program p buffers after rest observations final →
      Executed program p buffers heap (request :: rest) (⟨events, status, values⟩ :: observations) final

/-- Every intermediate host preparation, complete public call and bounded
readback belongs to this derived certificate. -/
inductive Calls [CInterface] (program : CCalls.Events.Program E) (p : Address) (buffers : Layout) :
    Heap → List Request → List (Nat → Option Value) → Heap → Prop where
  | nil : Calls program p buffers heap [] [] heap
  | cons : request.hostRun heap buffers = some ready →
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling (request.call p buffers).1 (request.call p buffers).2 ready .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, after⟩) →
      request.readback after buffers = values →
      Calls program p buffers after rest observations final →
      Calls program p buffers heap (request :: rest) (values :: observations) final

theorem trace [CInterface] (program : CCalls.Events.Program E)
    (get : ∀ heap, Float64Calls.QuietExecutionContract model program heap)
    (set : ∀ heap, Float64Set.QuietExecutionContract program heap)
    (requests : List Request) (stored : Instance heap p kind mode state time)
    (buffersStored : Stored heap buffers) (separate : buffers.Separate p)
    (fits : ∀ request ∈ requests, request.Fits buffers)
    (allowed : ∀ request ∈ requests, request.Allowed kind mode) :
    ∃ after, Calls program p buffers heap requests (expected model time requests state) after ∧
      Instance after p kind mode (finalState requests state) time ∧ Stored after buffers ∧
      CStorage.Preserves heap after ∧ CReadOnly.Preserves heap after ∧
      (∀ q, q ≠ StateProofs.stateAddress p → Outside buffers q → after q = heap q) := by
  induction requests generalizing heap state with
  | nil => exact ⟨heap, .nil, stored, buffersStored, .refl _, .refl _, fun _ _ _ => rfl⟩
  | cons request rest ih =>
    obtain ⟨prepared, called, instanceAfter, buffersAfter, observes, storageFrame, readonly, frame⟩ :=
      step program get set request stored buffersStored (fits request (by simp)) separate (allowed request (by simp))
    obtain ⟨after, following, finalInstance, finalBuffers, finalStorage, finalReadonly, finalFrame⟩ :=
      ih instanceAfter buffersAfter
        (fun request member => fits request (List.mem_cons_of_mem _ member))
        (fun request member => allowed request (List.mem_cons_of_mem _ member))
    exact ⟨after, .cons prepared called (Request.readback_correct observes) following,
      finalInstance, finalBuffers, storageFrame.trans finalStorage, readonly.trans finalReadonly,
      fun q other outside => (finalFrame q other outside).trans (frame q other outside)⟩

theorem Calls.executes [CInterface] {program : CCalls.Events.Program E}
    (certified : Calls program p buffers heap requests values after) :
    Executed program p buffers heap requests (values.map Observation.ok) after := by
  induction certified with
  | nil => exact .nil
  | cons prepared behavior output _ ih => exact .cons prepared ((behavior _).mpr rfl) output ih

theorem Calls.determines [CInterface] {program : CCalls.Events.Program E}
    (certified : Calls program p buffers heap requests values final)
    (executed : Executed program p buffers heap requests observed after) :
    observed = values.map Observation.ok ∧ after = final := by
  induction executed generalizing values final with
  | nil => cases certified; exact ⟨rfl, rfl⟩
  | cons prepared called output _ ih =>
    cases certified with
    | cons certifiedPreparation behavior expected following =>
      have sameReady := Option.some.inj (certifiedPreparation.symm.trans prepared)
      cases sameReady
      have returned := (behavior _).mp called
      cases returned
      have sameValues := output.symm.trans expected
      obtain ⟨tail, finish⟩ := ih following
      exact ⟨by simp only [List.map_cons, Observation.ok, sameValues, tail], finish⟩

theorem Calls.execution_iff [CInterface] {program : CCalls.Events.Program E}
    (certified : Calls program p buffers heap requests values final) :
    Executed program p buffers heap requests observed after ↔
      observed = values.map Observation.ok ∧ after = final := by
  constructor
  · exact certified.determines
  · rintro ⟨rfl, rfl⟩
    exact certified.executes

end Rumoca.FMI3.Float64Access
end
