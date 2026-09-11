import Parser.LocatedProofs
import Init.Data.String.Lemmas.Splits
import Init.Data.String.Lemmas.Pattern.Pred
import Init.Data.Iterators.Lemmas.Consumers.Loop

/-! Character-list specifications for the UTF-8 cursors used by span attachment.
These proofs use the standard string and iterator operations; runtime code is
unchanged. -/
namespace Parser.Source.Cursor
open String
open String.Slice.Pattern

theorem ofList_cons (c : Char) (cs : List Char) :
    String.ofList (c :: cs) = String.singleton c ++ String.ofList cs := by
  exact String.ofList_append (l₁ := [c]) (l₂ := cs)

private def search (predicate : Char → Bool) {s : String.Slice} (p : s.Pos) : Option s.Pos :=
  (Std.Iter.mk (α := ToForwardSearcher.DefaultForwardSearcher predicate s) ⟨p⟩).findSome?
    (fun | .matched start _ => some start | .rejected .. => none)

private theorem search_step (predicate : Char → Bool) {s : String.Slice} (p : s.Pos) :
    search predicate p = if h : p = s.endPos then none
      else if predicate (p.get h) then some p else search predicate (p.next h) := by
  unfold search
  rw [Std.Iter.findSome?_eq_match_step, Std.Iter.step_eq]
  simp only [Std.Iter.toIterM, ne_eq]
  by_cases h : p = s.endPos
  · simp [h]
  · have nonempty : (s.sliceFrom p).startPos ≠ (s.sliceFrom p).endPos := by
      intro same
      exact h (by simpa using congrArg Slice.Pos.ofSliceFrom same)
    have get : (s.sliceFrom p).startPos.get nonempty = p.get h := by
      simp only [Slice.Pos.get_eq_get_ofSliceFrom, Slice.Pos.ofSliceFrom_startPos]
    have dropped : ForwardPattern.dropPrefixOfNonempty? predicate (s.sliceFrom p) (by simpa using h) =
        if predicate (p.get h) then some ((s.sliceFrom p).startPos.next nonempty)
          else none := by
      change (if predicate ((s.sliceFrom p).startPos.get _) then _ else _) = _
      rw [get]
    simp only [h, ↓reduceDIte]
    split <;> rename_i heq
    · split at heq
      · rename_i pos' heq'
        have matched : predicate (p.get h) = true := by
          cases value : predicate (p.get h) with
          | false => simp [dropped, value] at heq'
          | true => rfl
        simp only [Id.run_pure, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield,
          Std.PlausibleIterStep.yield, Std.IterStep.yield.injEq] at heq
        rw [← heq.1, ← heq.2]
        simp [matched]
      · rename_i heq'
        have unmatched : ¬ predicate (p.get h) = true := by
          intro yes
          simp [dropped, yes] at heq'
        simp only [Id.run_pure, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield,
          Std.PlausibleIterStep.yield, Std.IterStep.yield.injEq] at heq
        rw [← heq.1, ← heq.2]
        simp [unmatched]
    · split at heq <;> simp at heq
    · split at heq <;> simp at heq

private theorem nextn_splits_slice {s : String.Slice} (p : s.Pos) (before : String)
    (chars : List Char) (rest : String)
    (split : p.Splits before (String.ofList chars ++ rest)) :
    (p.nextn chars.length).Splits (before ++ String.ofList chars) rest := by
  induction chars generalizing p before with
  | nil => simpa [Slice.Pos.nextn] using split
  | cons c cs ih =>
      have h : p.Splits before (String.singleton c ++ (String.ofList cs ++ rest)) := by
        simpa [ofList_cons, String.append_assoc] using split
      rw [List.length_cons, Slice.Pos.nextn, dif_pos h.ne_endPos_of_singleton]
      simpa only [ofList_cons, String.append_assoc]
        using ih (p.next h.ne_endPos_of_singleton) (before ++ String.singleton c) h.next

/-- Advancing by a token's character length consumes exactly its spelling,
including when characters occupy multiple UTF-8 bytes. -/
theorem nextn_splits {source : String} (p : source.Pos) (before : String)
    (chars : List Char) (rest : String)
    (split : p.Splits before (String.ofList chars ++ rest)) :
    (p.nextn chars.length).Splits (before ++ String.ofList chars) rest := by
  simpa [String.Pos.nextn, ← String.Pos.splits_toSlice_iff] using
    nextn_splits_slice p.toSlice before chars rest split.toSlice

private theorem search_gap (predicate : Char → Bool) {s : String.Slice}
    (p : s.Pos) (before : String) (gap : List Char) (c : Char) (rest : String)
    (split : p.Splits before (String.ofList gap ++ (String.singleton c ++ rest)))
    (trivia : gap.all (fun d => !predicate d) = true) (hit : predicate c = true) :
    search predicate p = some (p.nextn gap.length) := by
  induction gap generalizing p before with
  | nil =>
      have h : p.Splits before (String.singleton c ++ rest) := by simpa using split
      rw [search_step, dif_neg h.ne_endPos_of_singleton, h.next.get_eq_of_singleton, hit]
      rfl
  | cons d ds ih =>
      have h : p.Splits before
          (String.singleton d ++ (String.ofList ds ++ (String.singleton c ++ rest))) := by
        simpa only [ofList_cons, String.append_assoc] using split
      have both : predicate d = false ∧ ds.all (fun d => !predicate d) = true := by
        simpa using trivia
      have hd := both.1
      rw [search_step, dif_neg h.ne_endPos_of_singleton, h.next.get_eq_of_singleton, hd]
      simpa only [Bool.false_eq_true, ↓reduceIte, List.length_cons, Slice.Pos.nextn,
          dif_pos h.ne_endPos_of_singleton] using
        ih (p.next h.ne_endPos_of_singleton) (before ++ String.singleton d) h.next
          both.2

private theorem find_splits_slice (predicate : Char → Bool) (s : String.Slice)
    (gap : List Char) (c : Char) (rest : String)
    (text : s.copy = String.ofList gap ++ (String.singleton c ++ rest))
    (trivia : gap.all (fun d => !predicate d) = true) (hit : predicate c = true) :
    (s.find predicate).Splits (String.ofList gap) (String.singleton c ++ rest) := by
  have split : s.startPos.Splits "" (String.ofList gap ++ (String.singleton c ++ rest)) :=
    ⟨by simpa using text, by simp⟩
  change ((search predicate s.startPos).getD s.endPos).Splits _ _
  rw [search_gap predicate s.startPos "" gap c rest split trivia hit]
  simpa using nextn_splits_slice s.startPos "" gap (String.singleton c ++ rest) split

private theorem lift_splits {s : String.Slice} (p : s.Pos) (before rest : String)
    (split : p.Splits before rest) (q : (s.sliceFrom p).Pos) (left right : String)
    (found : q.Splits left right) : (Slice.Pos.ofSliceFrom q).Splits (before ++ left) right where
  eq_append := by
    have rest_eq : rest = left ++ right := by
      rw [← split.copy_sliceFrom_eq]
      exact found.eq_append
    rw [split.eq_append, rest_eq, String.append_assoc]
  offset_eq_rawEndPos := by
    simp [Slice.Pos.offset_ofSliceFrom, found.offset_eq_rawEndPos, split.offset_eq_rawEndPos,
      String.Pos.Raw.ext_iff, String.Pos.Raw.offsetBy]

/-- Finding the first nontrivia character preserves the exact skipped prefix.
The statement concerns the actual standard-library cursor used by `attach`. -/
theorem find_splits {source : String} (predicate : Char → Bool) (p : source.Pos)
    (before : String) (gap : List Char) (c : Char) (rest : String)
    (split : p.Splits before (String.ofList gap ++ (String.singleton c ++ rest)))
    (trivia : gap.all (fun d => !predicate d) = true) (hit : predicate c = true) :
    (p.find predicate).Splits (before ++ String.ofList gap) (String.singleton c ++ rest) := by
  have found := find_splits_slice predicate (source.toSlice.sliceFrom p.toSlice) gap c rest
    split.toSlice.copy_sliceFrom_eq trivia hit
  have lifted := lift_splits p.toSlice before _ split.toSlice _ _ _ found
  simpa [String.Pos.find, Slice.Pos.find, ← String.Pos.splits_toSlice_iff] using lifted

/-- Extracting between two characterized UTF-8 cursors yields their intervening
text exactly, without searching for another occurrence of that text. -/
theorem extract_between {source : String} (p q : source.Pos) (before text rest : String)
    (left : p.Splits before (text ++ rest)) (right : q.Splits (before ++ text) rest) :
    p ≤ q ∧ String.extract p q = text := by
  obtain ⟨order, copied⟩ := String.copy_slice_eq_iff_splits.mpr ⟨before, rest, left, right⟩
  exact ⟨order, (String.extract_eq_copy_slice p q order).trans copied⟩

end Parser.Source.Cursor
