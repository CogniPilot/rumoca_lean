import Parser.Scanner

/-! Compositional scanning judgments. A prefix is checked with its actual
remaining characters present, so composition cannot split a longest-match
word, number or symbol. This is a proof interface, not another scanner. -/
namespace Parser.Scanner

inductive Prefix (cfg : Config) : List Char → List Token → List Char → Prop where
  | done : Prefix cfg rest [] rest
  | space : cfg.space c = true → Prefix cfg cs ts rest → Prefix cfg (c :: cs) ts rest
  | word : cfg.space c = false → cfg.wordStart c = true →
      Prefix cfg (cs.dropWhile cfg.wordRest) ts rest →
      Prefix cfg (c :: cs)
        (cfg.classify (String.ofList (c :: cs.takeWhile cfg.wordRest)) :: ts) rest
  | number : cfg.space c = false → cfg.wordStart c = false → c.isDigit = true →
      Prefix cfg (cs.dropWhile cfg.numberRest) ts rest →
      Prefix cfg (c :: cs)
        (.literal (String.ofList (c :: cs.takeWhile cfg.numberRest)) :: ts) rest
  | symbol : cfg.space c = false → cfg.wordStart c = false → c.isDigit = false →
      SymbolLexes cfg (c :: cs) t tail → Prefix cfg tail ts rest →
      Prefix cfg (c :: cs) (t :: ts) rest

namespace Prefix

theorem append (first : Prefix cfg input ts middle) (last : Prefix cfg middle us rest) :
    Prefix cfg input (ts ++ us) rest := by
  induction first with
  | done => exact last
  | space hs _ ih => exact .space hs (ih last)
  | word hs hw _ ih => exact .word hs hw (ih last)
  | number hs hw hd _ ih => exact .number hs hw hd (ih last)
  | symbol hs hw hd sym _ ih => exact .symbol hs hw hd sym (ih last)

theorem finish (first : Prefix cfg input ts rest) (last : Lexes cfg rest us) :
    Lexes cfg input (ts ++ us) := by
  induction first with
  | done => exact last
  | space hs _ ih => exact .space hs (ih last)
  | word hs hw _ ih => exact .word hs hw (ih last)
  | number hs hw hd _ ih => exact .number hs hw hd (ih last)
  | symbol hs hw hd sym _ ih => exact .symbol hs hw hd sym (ih last)

theorem of_lexes (lexed : Lexes cfg input ts) : Prefix cfg input ts [] := by
  induction lexed with
  | nil => exact .done
  | space hs _ ih => exact .space hs ih
  | word hs hw _ ih => exact .word hs hw ih
  | number hs hw hd _ ih => exact .number hs hw hd ih
  | symbol hs hw hd sym _ ih => exact .symbol hs hw hd sym ih

theorem complete_iff : Prefix cfg input ts [] ↔ Lexes cfg input ts := by
  exact ⟨fun h => by simpa using h.finish .nil, of_lexes⟩

/-- Every remaining character is an unchanged suffix of the original input. -/
theorem suffix (read : Prefix cfg input ts rest) : ∃ consumed, input = consumed ++ rest := by
  induction read with
  | done => exact ⟨[], rfl⟩
  | @space c cs ts rest hs h ih =>
      obtain ⟨consumed, same⟩ := ih
      exact ⟨c :: consumed, by simp [same]⟩
  | @word c ts rest cs hs hw h ih =>
      obtain ⟨consumed, same⟩ := ih
      refine ⟨c :: (cs.takeWhile cfg.wordRest ++ consumed), ?_⟩
      rw [List.cons_append, List.append_assoc, ← same, List.takeWhile_append_dropWhile]
  | @number c ts rest cs hs hw hd h ih =>
      obtain ⟨consumed, same⟩ := ih
      refine ⟨c :: (cs.takeWhile cfg.numberRest ++ consumed), ?_⟩
      rw [List.cons_append, List.append_assoc, ← same, List.takeWhile_append_dropWhile]
  | @symbol c cs t tail ts rest hs hw hd sym h ih =>
      obtain ⟨consumed, same⟩ := ih
      cases sym with
      | single hp hs => exact ⟨c :: consumed, by simp [same]⟩
      | @pair _ d _ hp => exact ⟨c :: d :: consumed, by simp [same]⟩

theorem remaining_length (read : Prefix cfg input ts rest) : rest.length ≤ input.length := by
  obtain ⟨consumed, rfl⟩ := read.suffix
  simp

end Prefix
end Parser.Scanner
