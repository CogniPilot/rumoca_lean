import RumocaEFMI.Identity

namespace Rumoca.EFMI.Manifest.Identity

theorem matches_length (slots : List Slot) (cs : List Char) (h : Matches slots cs) :
    cs.length = slots.length := by
  induction slots generalizing cs with
  | nil => cases cs <;> simp_all [Matches]
  | cons slot slots ih =>
    cases cs with
    | nil => contradiction
    | cons c cs => exact congrArg Nat.succ (ih cs h.2)

theorem uuid_length (text : String) (h : UUID text) : text.toList.length = 38 :=
  matches_length uuidLayout text.toList h

theorem calendar_date (year month day : Nat) (h : Calendar year month day) :
    ∃ date : Std.Time.PlainDate,
      date.year.toInt = year ∧ date.month.val = month ∧ date.day.val = day := by
  unfold Calendar at h
  split at h
  · exact ⟨⟨_, _, _, h⟩, rfl, rfl, rfl⟩
  · contradiction

/-- The fields in the actual timestamp denote a valid Gregorian date and a
whole-second time of day. No external clock or date parser licenses this fact. -/
theorem utc_fields (text : String) (h : UTC text) :
    text.toList.length = 20 ∧
    ∃ date : Std.Time.PlainDate,
      date.year.toInt = digits text.toList 0 4 ∧
      date.month.val = digits text.toList 5 2 ∧
      date.day.val = digits text.toList 8 2 ∧
      (1 ≤ digits text.toList 0 4 ∧ digits text.toList 0 4 ≤ 9999) ∧
      digits text.toList 11 2 < 24 ∧ digits text.toList 14 2 < 60 ∧
      digits text.toList 17 2 < 60 := by
  obtain ⟨layout, year, calendar, hour, minute, second⟩ := h
  obtain ⟨date, dy, dm, dd⟩ := calendar_date _ _ _ calendar
  exact ⟨matches_length utcLayout _ layout, date, dy, dm, dd, year, hour, minute, second⟩

theorem valid_iff (identity : Identity) : identity.valid = true ↔ identity.Valid := by
  simp [valid]

theorem valid_distinct (identity : Identity) (h : identity.valid = true) :
    identity.container.toLower ≠ identity.algorithm.toLower ∧
    identity.container.toLower ≠ identity.production.toLower ∧
    identity.algorithm.toLower ≠ identity.production.toLower :=
  ((valid_iff identity).mp h).2.2.2.2

end Rumoca.EFMI.Manifest.Identity
