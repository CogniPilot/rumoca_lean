import Std

/-! Composable output ranges. Byte lengths are indices of document nodes, so
collecting nested annotations never renders or rescans a child to find its
length. Entries contain only byte offsets and compact origin references. -/
namespace Rumoca.Printed

inductive Doc (Origin : Type) : Nat → Type where
  | text (value : String) : Doc Origin value.utf8ByteSize
  | append (left : Doc Origin n) (right : Doc Origin m) : Doc Origin (n + m)
  | mark (origin : Origin) (body : Doc Origin n) : Doc Origin n

def Doc.render : Doc Origin n → String
  | .text value => value
  | .append left right => left.render ++ right.render
  | .mark _ body => body.render

theorem Doc.render_size (doc : Doc Origin n) : doc.render.utf8ByteSize = n := by
  induction doc with
  | text => rfl
  | append left right ihLeft ihRight => simp only [render, String.utf8ByteSize_append, *]
  | mark _ _ ih => exact ih

structure Entry (Origin : Type) where
  origin : Origin
  start : Nat
  stop : Nat
  deriving DecidableEq

def Doc.entries : Doc Origin n → Nat → List (Entry Origin)
  | .text _, _ => []
  | .append (n := leftSize) left right, start =>
      left.entries start ++ right.entries (start + leftSize)
  | .mark origin (n := size) body, start =>
      ⟨origin, start, start + size⟩ :: body.entries start

/-- The executable collector uses a single array accumulator. The list-valued
reference above specifies order and multiplicity, including duplicate ranges. -/
def Doc.entriesInto : Doc Origin n → Nat → Array (Entry Origin) → Array (Entry Origin)
  | .text _, _, acc => acc
  | .append (n := leftSize) left right, start, acc =>
      right.entriesInto (start + leftSize) (left.entriesInto start acc)
  | .mark origin (n := size) body, start, acc =>
      body.entriesInto start (acc.push ⟨origin, start, start + size⟩)

theorem Doc.entriesInto_eq (doc : Doc Origin n) (start : Nat) (acc : Array (Entry Origin)) :
    (doc.entriesInto start acc).toList = acc.toList ++ doc.entries start := by
  induction doc generalizing start acc with
  | text => simp [entriesInto, entries]
  | append left right ihLeft ihRight =>
      simp only [entriesInto, entries, ihRight, ihLeft, List.append_assoc]
  | mark origin body ih => simp [entriesInto, entries, ih, List.append_assoc]

/-- An independent textual decomposition for one annotation occurrence. It
identifies the exact prefix and segment, rather than just in-bounds offsets. -/
inductive Region {Origin : Type} : {n : Nat} → Doc Origin n → Origin → String → String → String → Prop where
  | here (origin : Origin) (body : Doc Origin n) :
      Region (.mark origin body) origin "" body.render ""
  | marked (region : Region body origin beforeText segment suffix) :
      Region (.mark outer body) origin beforeText segment suffix
  | left {lhs : Doc Origin n} (region : Region lhs origin beforeText segment suffix)
      (rhs : Doc Origin m) :
      Region (.append lhs rhs) origin beforeText segment (suffix ++ rhs.render)
  | right {rhs : Doc Origin m} (lhs : Doc Origin n)
      (region : Region rhs origin beforeText segment suffix) :
      Region (.append lhs rhs) origin (lhs.render ++ beforeText) segment suffix

theorem Region.render_eq (region : Region doc origin beforeText segment suffix) :
    doc.render = beforeText ++ segment ++ suffix := by
  induction region with
  | here => simp [Doc.render]
  | marked _ ih => exact ih
  | left _ _ ih => simp only [Doc.render, ih, String.append_assoc]
  | right _ _ ih => simp only [Doc.render, ih, String.append_assoc]

/-- The numeric range extracts precisely the segment's UTF-8 bytes, including
when preceding text or the segment itself contains multibyte characters. -/
theorem Region.bytes (region : Region doc origin beforeText segment suffix) :
    doc.render.toByteArray.extract beforeText.utf8ByteSize
      (beforeText.utf8ByteSize + segment.utf8ByteSize) = segment.toByteArray := by
  rw [region.render_eq, String.append_assoc]
  simp only [String.toByteArray_append, ← String.size_toByteArray]
  change (beforeText.toByteArray ++ (segment.toByteArray ++ suffix.toByteArray)).extract
    (beforeText.toByteArray.size + 0) (beforeText.toByteArray.size + segment.toByteArray.size) = _
  rw [ByteArray.extract_append_size_add]
  exact ByteArray.extract_append_eq_left rfl

theorem Region.mem_entries {doc : Doc Origin n}
    (region : Region doc origin beforeText segment suffix) (start : Nat) :
    (⟨origin, start + beforeText.utf8ByteSize,
      start + beforeText.utf8ByteSize + segment.utf8ByteSize⟩ : Entry Origin) ∈ doc.entries start := by
  induction region generalizing start with
  | here origin body => simp [Doc.entries, Doc.render_size]
  | marked region ih => exact List.mem_cons_of_mem _ (ih start)
  | left region right ih => exact List.mem_append_left _ (ih start)
  | right left region ih =>
      apply List.mem_append_right
      simpa only [String.utf8ByteSize_append, Doc.render_size, Nat.add_assoc] using
        ih (start + _)

theorem Doc.entries_region (doc : Doc Origin n) (start : Nat) (entry : Entry Origin)
    (member : entry ∈ doc.entries start) :
    ∃ beforeText segment suffix, Region doc entry.origin beforeText segment suffix ∧
      entry.start = start + beforeText.utf8ByteSize ∧
      entry.stop = entry.start + segment.utf8ByteSize := by
  induction doc generalizing start with
  | text => simp [entries] at member
  | append left right ihLeft ihRight =>
      rcases List.mem_append.mp member with member | member
      · obtain ⟨beforeText, segment, suffix, region, first, last⟩ := ihLeft start member
        exact ⟨beforeText, segment, suffix ++ right.render, .left region right, first, last⟩
      · obtain ⟨beforeText, segment, suffix, region, first, last⟩ := ihRight _ member
        refine ⟨left.render ++ beforeText, segment, suffix, .right left region, ?_, last⟩
        simpa only [String.utf8ByteSize_append, render_size, Nat.add_assoc] using first
  | mark origin body ih =>
      rcases List.mem_cons.mp member with same | member
      · subst entry
        exact ⟨"", body.render, "", .here origin body, by simp, by simp [render_size]⟩
      · obtain ⟨beforeText, segment, suffix, region, first, last⟩ := ih start member
        exact ⟨beforeText, segment, suffix, .marked region, first, last⟩

/-- Exact, complete source-map correspondence for the actual array collector.
The preceding list equality additionally preserves order and multiplicity. -/
theorem Doc.map_iff (doc : Doc Origin n) (entry : Entry Origin) :
    entry ∈ doc.entriesInto 0 #[] ↔
    ∃ beforeText segment suffix, Region doc entry.origin beforeText segment suffix ∧
      entry.start = beforeText.utf8ByteSize ∧
      entry.stop = entry.start + segment.utf8ByteSize := by
  rw [← Array.mem_toList_iff, entriesInto_eq]
  simp only [List.nil_append]
  constructor
  · intro member
    simpa only [Nat.zero_add] using doc.entries_region 0 entry member
  · rintro ⟨beforeText, segment, suffix, region, first, last⟩
    have member := region.mem_entries 0
    simpa only [Nat.zero_add, ← first, ← last] using member

theorem Doc.map_bounds (doc : Doc Origin n) (entry : Entry Origin)
    (member : entry ∈ doc.entriesInto 0 #[]) :
    entry.start ≤ entry.stop ∧ entry.stop ≤ doc.render.utf8ByteSize := by
  obtain ⟨beforeText, segment, suffix, region, first, last⟩ := (doc.map_iff entry).mp member
  rw [region.render_eq]
  simp only [String.utf8ByteSize_append]
  omega

def Doc.EveryOrigin (check : Origin → Prop) : Doc Origin n → Prop
  | .text _ => True
  | .append left right => left.EveryOrigin check ∧ right.EveryOrigin check
  | .mark origin body => check origin ∧ body.EveryOrigin check

theorem Region.origin_checked {doc : Doc Origin n}
    (region : Region doc origin beforeText segment suffix)
    (check : Origin → Prop) (checked : doc.EveryOrigin check) : check origin := by
  induction region with
  | here => exact checked.1
  | marked _ ih => exact ih checked.2
  | left _ _ ih => exact ih checked.1
  | right _ _ ih => exact ih checked.2

theorem Doc.map_every (doc : Doc Origin n) (check : Origin → Prop)
    (checked : doc.EveryOrigin check) (entry : Entry Origin)
    (member : entry ∈ doc.entriesInto 0 #[]) : check entry.origin := by
  obtain ⟨_, _, _, region, _, _⟩ := (doc.map_iff entry).mp member
  exact region.origin_checked check checked

end Rumoca.Printed
