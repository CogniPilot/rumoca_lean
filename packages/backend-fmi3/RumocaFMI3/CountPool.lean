import RumocaFMI3.CountContract

/-! Construct static literal bindings for count-query failures from the actual
adapter function list. The original, untransformed functions execute here;
native allocation, header interpretation and enabled callbacks remain open. -/
namespace Rumoca.FMI3.CountQueries
open CTree CMemory CLiteral LiteralPreparation

def failureMessage (missing : Bool) : String :=
  if missing then "Missing output pointer" else "Call is not allowed in the current FMI state"

def FailureCondition (missing : Bool) (kind : Kind) (mode : Mode) (buffer : Option Address) : Prop :=
  if missing then buffer = none ∧ Reference.Allowed .getCounts kind mode
  else ¬ Reference.Allowed .getCounts kind mode

theorem message_collected (m : Solve.FMI3Model source) (events missing : Bool) :
    failureMessage missing ∈ functionTexts (Runtime.function m (signature events)) := by
  cases events <;> cases missing <;>
    simp [Runtime.function, Runtime.body, signature, outputName, failureMessage,
      functionTexts, statementTexts, expressionTexts, Runtime.require,
      Runtime.instancePrefix, Runtime.pointerCheck, Runtime.reject, Runtime.branch,
      Runtime.fail, Runtime.ret, Runtime.call, Runtime.v]

noncomputable section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

theorem failure_reaches (m : Solve.FMI3Model source) (events missing : Bool)
    (program : CCalls.Program) (heap : Heap) (p message : Address) (buffer : Option Address)
    (kind : Kind) (mode : Mode) (logger : Option Address) (stack : CCalls.Typed.Continuation)
    (defined : program.definitions (signature events).name = some (.tree (Runtime.function m (signature events))))
    (helper : program.definitions "fail" = some (.tree Runtime.helpers[0]))
    (literal : static.addresses (failureMessage missing) = some message)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (hl : load heap (p.member "logger") = some (.pointer logger))
    (hg : load heap (p.member "logging") = some (.integer 0))
    (condition : FailureCondition missing kind mode buffer) :
    Transition.Reaches (CCalls.Typed.machine program).step
      (.calling (signature events).name (arguments (some p) buffer) heap stack)
      (.returning (.integer 3) (LifecycleBodies.writeMode heap p .terminated) stack) := by
  cases missing with
  | false =>
      exact rejected_reaches m events program heap p message buffer kind mode logger stack
        defined helper literal hk hm hl hg condition
  | true =>
      obtain ⟨rfl, allowed⟩ := condition
      exact missing_reaches m events program heap p message kind mode logger stack
        defined helper literal hk hm hl hg allowed

omit static in
/-- Complete failure behavior with a collected address and installed read-only
objects. Instance cells must already exist outside the fresh literal blocks. -/
theorem prepared_failure (m : Solve.FMI3Model source) (sigs : List Signature)
    {pool : Pool (excluded ++ (functions m sigs).flatMap functionNames)}
    (made : prepare m sigs = some pool)
    (unique : ((functions m sigs).map (fun fn => fn.signature.name)).Nodup)
    (events missing : Bool) (member : signature events ∈ sigs)
    (before : Heap) (firstBlock : Nat) (signed : Bool)
    (fresh : ∀ entry ∈ pool.entries, ∀ address,
      address.block = firstBlock + entry.slot → before address = none)
    (p : Address) (buffer : Option Address) (kind : Kind) (mode : Mode) (logger : Option Address)
    (hk : load before (p.member "kind") = some (.integer kind.code))
    (hm : before (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (hl : load before (p.member "logger") = some (.pointer logger))
    (hg : load before (p.member "logging") = some (.integer 0))
    (condition : FailureCondition missing kind mode buffer) :
    (∀ behavior, (@CCalls.Typed.machine (cInterface (pool.addresses firstBlock))
      (program m sigs)).Behaves
      (.calling (signature events).name (arguments (some p) buffer)
        (pool.install before firstBlock signed) .done) behavior ↔
      behavior = .terminates ⟨.integer 3,
        LifecycleBodies.writeMode (pool.install before firstBlock signed) p .terminated⟩) ∧
    (∀ q, q ≠ p.member "mode" →
      LifecycleBodies.writeMode (pool.install before firstBlock signed) p .terminated q =
        pool.install before firstBlock signed q) ∧
    Valid (pool.addresses firstBlock) signed
      (LifecycleBodies.writeMode (pool.install before firstBlock signed) p .terminated) := by
  obtain ⟨message, literal⟩ := message_bound m sigs made _ member _
    (message_collected m events missing) firstBlock
  have steps := failure_reaches (static := ⟨pool.addresses firstBlock⟩) m events missing
    (program m sigs) (pool.install before firstBlock signed) p message buffer kind mode logger .done
    (function_bound m sigs unique _ member)
    (helpers_bound m sigs Runtime.helpers[0] (by simp [Runtime.helpers])) literal
    (pool.install_load before firstBlock signed fresh _ _ hk)
    (pool.install_existing (signed := signed) fresh hm)
    (pool.install_load before firstBlock signed fresh _ _ hl)
    (pool.install_load before firstBlock signed fresh _ _ hg) condition
  refine ⟨fun behavior => ?_, ?_, ?_⟩
  · exact (@CCalls.Typed.machine (cInterface (pool.addresses firstBlock)) (program m sigs)).behavior_iff
      (steps.trans (.next rfl (.refl _))) rfl
  · intro q different
    exact replace_other _ _ _ _ different
  · exact (pool.storage_valid before firstBlock signed).preserved
      (@CReadOnly.typed_reaches (cInterface (pool.addresses firstBlock)) (program m sigs) _ _ steps)

end
end Rumoca.FMI3.CountQueries
