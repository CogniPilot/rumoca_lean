import RumocaFMI3.InstanceSlot
import RumocaC.MemoryFootprint

namespace Rumoca.FMI3.InstanceInitialization
open CMemory

private theorem writable_region (agreement : Set.EqOn before after region) (inside : address ∈ region)
    (writable : Reset.Writable before address type) : Reset.Writable after address type := by
  obtain ⟨value, found⟩ := writable
  exact ⟨value, (agreement inside).symm.trans found⟩

/-- Whole-cell agreement on the instance retains its writable storage,
including the nested prepared model field. -/
theorem Storage.region (storage : Storage before p)
    (agreement : Set.EqOn before after {q | p.InRecord q}) : Storage after p := by
  have field (name : String) {type : CType} := writable_region (type := type) agreement (p.member_in_record name)
  have state := writable_region (type := .float64) agreement ((p.member_in_record "model").member "x")
  rcases storage with ⟨⟨hx, ht, hn, he, hc, hs, hd, hm⟩, hk, hv, hl, hg⟩
  exact ⟨⟨state hx, field "time" ht, field "timeMin" hn, field "eventTime" he,
    field "lastCompleted" hc, field "stop" hs, field "stopDefined" hd, field "mode" hm⟩,
    field "kind" hk, field "environment" hv, field "logger" hl, field "logging" hg⟩

/-- Transfer the complete initialized-value postcondition, not only cell
types. No statement is made about unrelated instances or caller buffers. -/
theorem Initialized.region (initialized : Initialized before p kind environment logger logging)
    (agreement : Set.EqOn before after {q | p.InRecord q}) :
    Initialized after p kind environment logger logging := by
  have field (name : String) := CMemory.Footprint.load_eq agreement (p.member_in_record name)
  refine ⟨initialized.storage.region agreement, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (CMemory.Footprint.load_eq agreement ((p.member_in_record "model").member "x")).symm.trans initialized.model
  · rcases initialized.clock with ⟨ht, hn, he, hc⟩
    exact ⟨(agreement (p.member_in_record "time")).symm.trans ht,
      (agreement (p.member_in_record "timeMin")).symm.trans hn,
      (agreement (p.member_in_record "eventTime")).symm.trans he,
      (agreement (p.member_in_record "lastCompleted")).symm.trans hc⟩
  · exact (field "mode").symm.trans initialized.modeValue
  · exact (field "kind").symm.trans initialized.kindValue
  · exact (field "environment").symm.trans initialized.environmentValue
  · exact (field "logger").symm.trans initialized.loggerValue
  · exact (field "logging").symm.trans initialized.loggingValue
  · exact (field "stop").symm.trans initialized.stopValue
  · exact (field "stopDefined").symm.trans initialized.stopDefinedValue

end Rumoca.FMI3.InstanceInitialization

namespace Rumoca.FMI3.InstanceSlot
open CMemory

theorem initialized_region
    (agreement : Set.EqOn (finalHeap heap p slot kind environment logger logging) after {q | p.InRecord q})
    (bounded : slot < 2^64) :
    InstanceInitialization.Initialized after p kind environment logger logging ∧
    Storage after p ∧ load after (p.member "slot") = some (.integer slot) := by
  refine ⟨(initialized heap p slot kind environment logger logging).region agreement, ?_, ?_⟩
  · exact ⟨(storage_ready heap p slot kind environment logger logging).fields.region agreement,
      ⟨some (.integer slot), (agreement (p.member_in_record "slot")).symm.trans
        (final_index heap p slot kind environment logger logging)⟩⟩
  · exact (CMemory.Footprint.load_eq agreement (p.member_in_record "slot")).symm.trans
      (metadata heap p slot kind environment logger logging bounded)

end Rumoca.FMI3.InstanceSlot
