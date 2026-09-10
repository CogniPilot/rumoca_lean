import RumocaEFMI.Archive
import RumocaEFMI.ZIPProofs

namespace Rumoca.EFMI.Archive
open StoredZIP

theorem entry_names (code : Code) : (entries code).map Entry.name = paths := by
  simp only [entries, Code.entries, schemaEntries, paths, List.map_append, List.map_map]
  rfl

theorem paths_unique : paths.Nodup := by decide +kernel

theorem member_count (code : Code) : (entries code).length = 50 := by
  have count : paths.length = 50 := by decide +kernel
  simpa only [List.length_map] using (congrArg List.length (entry_names code)).trans count

theorem code_mem (code : Code) (member : Member) :
    (⟨member.name, (code.text member).toUTF8⟩ : Entry) ∈ entries code := by
  apply List.mem_append_left
  apply List.mem_map.mpr
  exact ⟨member, by cases member <;> simp [members], rfl⟩

theorem schema_mem (code : Code) (resource : Resources.Resource) (h : resource ∈ Resources.schemas) :
    (⟨resource.name, resource.text.toUTF8⟩ : Entry) ∈ entries code := by
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨resource, h, rfl⟩

/-- Name uniqueness makes lookup independent of the member's list position. -/
theorem lookup_of_mem (items : List Entry) (unique : (items.map Entry.name).Nodup)
    (entry : Entry) (mem : entry ∈ items) : lookup items entry.name = some entry.bytes := by
  induction items with
  | nil => simp at mem
  | cons head rest ih =>
    have hn := List.nodup_cons.mp unique
    rcases List.mem_cons.mp mem with same | mem
    · subst head
      simp [lookup]
    · have different : head.name ≠ entry.name := by
        intro same
        exact hn.1 (List.mem_map.mpr ⟨entry, mem, same.symm⟩)
      simpa [lookup, different] using ih hn.2 mem

theorem code_lookup (code : Code) (member : Member) :
    lookup (entries code) member.name = some (code.text member).toUTF8 :=
  lookup_of_mem _ (entry_names code ▸ paths_unique) _ (code_mem code member)

theorem schema_lookup (code : Code) (resource : Resources.Resource)
    (h : resource ∈ Resources.schemas) :
    lookup (entries code) resource.name = some resource.text.toUTF8 :=
  lookup_of_mem _ (entry_names code ▸ paths_unique) _ (schema_mem code resource h)

theorem encode_correct (code : Code) (h : encode code = .ok bytes) :
    Format.Conforms (entries code) bytes := StoredZIP.encode_sound h

end Rumoca.EFMI.Archive
