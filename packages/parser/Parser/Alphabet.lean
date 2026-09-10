import Parser.Regex
import Parser.Token

/-! Alphabet compression must reflect original symbols, not just mapped words.
Unknown symbols have code zero, distinct from every grammar terminal. -/
namespace Parser.Alphabet

deriving instance ReflBEq, LawfulBEq for Symbol

def encode (alphabet : Array Symbol) (s : Symbol) : Fin (alphabet.size + 1) :=
  ⟨((alphabet.findIdx? (· == s)).map (· + 1) |>.getD 0) % (alphabet.size + 1),
    Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem encode_injective_at (alphabet : Array Symbol) (a b : Symbol) (ha : a ∈ alphabet)
    (he : encode alphabet a = encode alphabet b) : a = b := by
  obtain ⟨i, hi⟩ : ∃ i, alphabet.findIdx? (· == a) = some i := by
    exact ⟨_, Array.findIdx?_eq_some_of_exists ⟨a, ha, by simp⟩⟩
  obtain ⟨hilt, hia, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp hi
  have hv := congrArg Fin.val he
  simp only [encode, hi, Option.map_some, Option.getD_some] at hv
  cases hb : alphabet.findIdx? (· == b) with
  | none =>
    simp only [hb, Option.map_none, Option.getD_none, Nat.zero_mod] at hv
    rw [Nat.mod_eq_of_lt (by omega)] at hv
    omega
  | some j =>
    obtain ⟨hjlt, hjb, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp hb
    simp only [hb, Option.map_some, Option.getD_some] at hv
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv
    have hij : i = j := by omega
    subst j
    exact (eq_of_beq hia).symm.trans (eq_of_beq hjb)

def atoms : RE α → List α
  | .char a => [a]
  | .plus a b | .comp a b => atoms a ++ atoms b
  | .star a => atoms a
  | _ => []

theorem accepted_atoms (r : RE α) (h : r.Accepts xs) : ∀ a ∈ xs, a ∈ atoms r := by
  induction r generalizing xs with
  | zero => cases h
  | epsilon => cases h; simp
  | char a => cases h; simp [atoms]
  | plus r s hr hs =>
    rcases h with h | h
    · intro a ha; exact List.mem_append_left _ (hr h a ha)
    · intro a ha; exact List.mem_append_right _ (hs h a ha)
  | comp r s hr hs =>
    obtain ⟨as, ha, bs, hb, rfl⟩ := Language.mem_mul.mp h
    intro a hm
    rcases List.mem_append.mp hm with hm | hm
    · exact List.mem_append_left _ (hr ha a hm)
    · exact List.mem_append_right _ (hs hb a hm)
  | star r hr =>
    obtain ⟨words, rfl, hw⟩ := Language.mem_kstar.mp h
    intro a ha
    obtain ⟨word, hm, ha⟩ := List.mem_flatten.mp ha
    exact hr (hw word hm) a ha

private theorem list_reflect (f : α → β) (xs ys : List α)
    (h : ∀ a ∈ xs, ∀ b, f a = f b → a = b) (he : xs.map f = ys.map f) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons a as ih =>
    cases ys with
    | nil => simp at he
    | cons b bs =>
      obtain ⟨hab, ht⟩ := List.cons.inj he
      have hab := h a (by simp) b hab
      subst b
      congr 1
      exact ih bs (fun c hc => h c (by simp [hc])) ht

/-- Lossless compression on grammar support suffices even when the entire
(infinite) input alphabet is not injectively encoded. -/
theorem reflects (r : RE α) (f : α → β)
    (hf : ∀ a ∈ atoms r, ∀ b, f a = f b → a = b) (xs : List α) :
    (r.map f).Accepts (xs.map f) ↔ r.Accepts xs := by
  simp only [RegularExpression.Accepts, RegularExpression.matches'_map, Language.map,
    RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  constructor
  · rintro ⟨ys, hy, he⟩
    have he := list_reflect f ys xs (fun a ha => hf a (accepted_atoms r hy a ha)) he
    exact he ▸ hy
  · intro h; exact ⟨xs, h, rfl⟩

theorem encode_reflects (alphabet : Array Symbol) (r : RE Symbol)
    (h : ∀ a ∈ atoms r, a ∈ alphabet) (xs : List Symbol) :
    (r.map (encode alphabet)).Accepts (xs.map (encode alphabet)) ↔ r.Accepts xs :=
  reflects r _ (fun a ha b he => encode_injective_at alphabet a b (h a ha) he) xs

end Parser.Alphabet
