import RumocaFMI3.LiteralPreparation
import RumocaFMI3.ErrorCalls

/-! Instantiate the existing rejected public-call proof with collected static
storage and the renderer's constructed definition table. This does not model
enabled callbacks or certify the complete adapter translation unit. -/
namespace Rumoca.FMI3.LiteralRejection
open CTree CMemory CLiteral LiteralPreparation
set_option autoImplicit false
variable {source : AST.Model}

theorem rejection_message_collected (m : Solve.FMI3Model source) :
    ErrorCalls.rejectionMessage ∈ functionTexts (Runtime.function m ErrorCalls.nominalSignature) := by
  simp [Runtime.function, Runtime.body, ErrorCalls.nominalSignature,
    ErrorCalls.rejectionMessage, functionTexts, statementTexts, expressionTexts,
    Runtime.require, Runtime.instancePrefix, Runtime.reject, Runtime.branch,
    Runtime.fail, Runtime.ret, Runtime.call, Runtime.v]

theorem rejection_message_bound (m : Solve.FMI3Model source) (signatures : List Signature)
    {pool : Pool (excluded ++ (functions m signatures).flatMap functionNames)}
    (made : prepare m signatures = some pool)
    (member : ErrorCalls.nominalSignature ∈ signatures) (firstBlock : Nat) :
    ∃ message, pool.addresses firstBlock ErrorCalls.rejectionMessage = some message := by
  have occurrence : ∃ fn ∈ functions m signatures,
      ErrorCalls.rejectionMessage ∈ functionTexts fn :=
    ⟨Runtime.function m ErrorCalls.nominalSignature,
      List.mem_append_right _ (List.mem_map.mpr ⟨_, member, rfl⟩), rejection_message_collected m⟩
  obtain ⟨name, named⟩ := (Pool.forFunctions_coverage made).mpr occurrence
  simp only [Pool.symbols, Option.map_eq_some_iff] at named
  obtain ⟨entry, found, rfl⟩ := named
  exact ⟨entry.address firstBlock, by simp [Pool.addresses, found]⟩

noncomputable section

private theorem installed_load {reserved : List String} (pool : Pool reserved)
    (before : Heap) (firstBlock : Nat) (signed : Bool)
    (fresh : ∀ entry ∈ pool.entries, ∀ address,
      address.block = firstBlock + entry.slot → before address = none)
    (address : Address) (value : Value) (loaded : load before address = some value) :
    load (pool.install before firstBlock signed) address = some value := by
  cases found : before address with
  | none => simp [load, found] at loaded
  | some object =>
      have kept := pool.install_existing (signed := signed) fresh found
      simpa only [load, kept, found] using loaded

/-- No literal address, storage object or function-table binding is supplied.
The checked pool and renderer's table construct them. This covers both kinds
in Instantiated, arbitrary output pointers/counts, and disabled logging. -/
theorem nominal_reject (m : Solve.FMI3Model source) (signatures : List Signature)
    {pool : Pool (excluded ++ (functions m signatures).flatMap functionNames)}
    (made : prepare m signatures = some pool)
    (unique : ((functions m signatures).map (fun fn => fn.signature.name)).Nodup)
    (member : ErrorCalls.nominalSignature ∈ signatures)
    (before : Heap) (firstBlock : Nat) (signed : Bool)
    (fresh : ∀ entry ∈ pool.entries, ∀ address,
      address.block = firstBlock + entry.slot → before address = none)
    (p : Address) (buffer : Option Address) (count : UInt64)
    (kind : Kind) (logger : Option Address)
    (hk : load before (p.member "kind") = some (.integer kind.code))
    (hm : before (p.member "mode") =
      some ⟨.int32, true, some (.integer Mode.instantiated.code)⟩)
    (hl : load before (p.member "logger") = some (.pointer logger))
    (hg : load before (p.member "logging") = some (.integer 0)) :
    (∀ behavior,
      (@CCalls.Typed.machine (pool.namedInterface cInterface firstBlock)
        (Lowering.program pool.symbols (program m signatures))).Behaves
        (.calling ErrorCalls.nominalSignature.name (ErrorCalls.nominalArguments p buffer count)
          (pool.install before firstBlock signed) .done) behavior ↔
        behavior = .terminates ⟨.integer 3,
          LifecycleBodies.writeMode (pool.install before firstBlock signed) p .terminated⟩) ∧
    (∀ q, q ≠ p.member "mode" →
      LifecycleBodies.writeMode (pool.install before firstBlock signed) p .terminated q =
        pool.install before firstBlock signed q) ∧
    Valid (pool.addresses firstBlock) signed
      (LifecycleBodies.writeMode (pool.install before firstBlock signed) p .terminated) := by
  obtain ⟨message, bound⟩ := rejection_message_bound m signatures made member firstBlock
  have hk' := installed_load pool before firstBlock signed fresh _ _ hk
  have hm' := pool.install_existing (signed := signed) fresh hm
  have hl' := installed_load pool before firstBlock signed fresh _ _ hl
  have hg' := installed_load pool before firstBlock signed fresh _ _ hg
  have defined := function_bound m signatures unique _ member
  have helper := helpers_bound m signatures Runtime.helpers[0] (by simp [Runtime.helpers])
  have correct := ErrorCalls.nominal_reject_correct (static := ⟨pool.addresses firstBlock⟩)
    m (program m signatures) (pool.install before firstBlock signed) p message buffer count
    kind logger signed defined helper bound
    (pool.storage_valid before firstBlock signed _ _ bound) hk' hm' hl' hg'
  refine ⟨fun behavior => ?_, correct.2.1, ?_⟩
  · exact (lowering_behaviors m signatures made firstBlock _ _ _ behavior).trans (correct.1 behavior)
  · have steps := ErrorCalls.nominal_reject_reaches (static := ⟨pool.addresses firstBlock⟩)
      m (program m signatures) (pool.install before firstBlock signed) p message buffer count
      kind logger .done defined helper bound hk' hm' hl' hg'
    exact (pool.storage_valid before firstBlock signed).preserved
      (@CReadOnly.typed_reaches (cInterface (pool.addresses firstBlock))
        (program m signatures) _ _ steps)

end
end Rumoca.FMI3.LiteralRejection
