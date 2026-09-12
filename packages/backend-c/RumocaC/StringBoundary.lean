import RumocaC.StringEnvelope

/-! Ordinary literal boundaries for the existing ASCII/octet C string profile.
The atom decoder is only a proof device. These results compose the independent
literal grammar with arbitrary following source characters; encoded prefixes
and phase-six adjacent-literal concatenation remain separate obligations. -/
namespace Rumoca.CString

/-- The closing quote and the following source are uniquely determined, even
when both candidate literal bodies are followed by arbitrary characters. -/
theorem Fragments.boundary_unique (first : Fragments a xs) (second : Fragments b ys)
    (same : a ++ '"' :: restA = b ++ '"' :: restB) :
    a = b ∧ xs = ys ∧ restA = restB := by
  obtain ⟨bodies, rests⟩ := first.envelope.boundary_unique second.envelope same
  exact ⟨bodies, Fragments.unique (bodies ▸ first) second, rests⟩

/-- An ordinary literal token cannot consume a different number of source
characters or denote different bytes on the same actual input. -/
theorem literal_boundary_unique (first : Denotes a xs) (second : Denotes b ys)
    (same : a ++ restA = b ++ restB) : a = b ∧ xs = ys ∧ restA = restB := by
  obtain ⟨bodyA, bytesA, textA, fragmentsA, valueA⟩ := first
  obtain ⟨bodyB, bytesB, textB, fragmentsB, valueB⟩ := second
  rw [textA, textB] at same
  have bodies : bodyA ++ '"' :: restA = bodyB ++ '"' :: restB := by
    have trimmed : (bodyA ++ ['"']) ++ restA = (bodyB ++ ['"']) ++ restB :=
      (List.cons.inj same).2
    simpa only [List.append_assoc, List.singleton_append] using trimmed
  obtain ⟨texts, bytes, rests⟩ := fragmentsA.boundary_unique fragmentsB bodies
  exact ⟨by rw [textA, textB, texts], by rw [valueA, valueB, bytes], rests⟩

/-- Prefix-free ordinary literals: a complete literal cannot be the proper
prefix of another complete literal in the authored C string grammar. -/
theorem literal_prefix_free (first : Denotes a xs) (second : Denotes b ys)
    (starts : a <+: b) : a = b ∧ xs = ys := by
  obtain ⟨rest, text⟩ := starts
  have result := literal_boundary_unique (restA := rest) (restB := []) first second
    (by simpa using text)
  exact ⟨result.1, result.2.1⟩

/-- The actual quote printer leaves exactly the supplied continuation. -/
theorem quote_boundary (source : String) (candidate : Denotes text bytes)
    (same : (CTree.quote source).toList ++ rest = text ++ after) :
    text = (CTree.quote source).toList ∧
      bytes = source.toUTF8.data.toList ++ [0] ∧ after = rest := by
  have result := literal_boundary_unique (quote_correct source) candidate same
  exact ⟨result.1.symm, result.2.1.symm, result.2.2.symm⟩

end Rumoca.CString
