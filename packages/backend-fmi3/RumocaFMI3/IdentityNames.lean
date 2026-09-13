import RumocaFMI3.IdentifierProofs
import RumocaFMI3.Metadata
import RumocaC.StringASCII

/-! Source identifier character rules ensure that the generated instantiation
token is not truncated by C string semantics. No producer assertion about the
token's byte validity is needed once those lexical premises are supplied. -/
namespace Rumoca.FMI3
open _root_.Parser CStringMemory

private theorem identifier_ascii {c : Char} (valid : identRest c = true) :
    0 < c.toNat ∧ c.toNat < 128 := by
  simp only [identRest, identStart, asciiLetter, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq, Char.isDigit, Char.le_def, UInt32.le_iff_toNat_le] at valid
  unfold Char.toNat
  rcases valid with (((range | range) | rfl) | range)
  · change 97 ≤ c.val.toNat ∧ c.val.toNat ≤ 122 at range
    omega
  · change 65 ≤ c.val.toNat ∧ c.val.toNat ≤ 90 at range
    omega
  · decide +kernel
  · change 48 ≤ c.val.toNat ∧ c.val.toNat ≤ 57 at range
    omega

theorem NameParts.nonzero_ascii (valid : NameParts name) : NonzeroASCII name := by
  obtain ⟨c, cs, chars, first, rest⟩ := valid
  intro byte member
  rw [chars] at member
  rcases List.mem_cons.mp member with rfl | member
  · exact identifier_ascii (by simp [identRest, first])
  · exact identifier_ascii (List.all_eq_true.mp rest byte member)

theorem Identity.token_ascii (model : Solve.FMI3Model source)
    (name : NameParts model.name) (state : NameParts model.stateName) : NonzeroASCII (token model) :=
  (((show NonzeroASCII "lean-rumoca-unit-v1:" from by unfold NonzeroASCII; decide +kernel).append
    name.nonzero_ascii).append (by unfold NonzeroASCII; decide +kernel)).append state.nonzero_ascii

theorem Identity.token_content (model : Solve.FMI3Model source)
    (name : NameParts model.name) (state : NameParts model.stateName) :
    content (token model) = (token model).toUTF8.data.toList := (token_ascii model name state).content

end Rumoca.FMI3
