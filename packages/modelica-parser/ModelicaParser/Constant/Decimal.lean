import Parser.Token

/-! Lexical value of a signed decimal literal spelling. The frontend recognizes
the MLS 3.7 unsigned-real form (digits, optional fraction, optional exponent)
with an optional sign, and records the exact base-ten content. The binary64
rounding of this content is a separate target contract in the core. -/
namespace Rumoca.ConstantProfile
open _root_.Parser

/-- The base-ten content of a literal: `value = sign * mantissa * 10 ^ power`. -/
structure Decimal where
  sign : Int
  mantissa : Nat
  power : Int
  deriving Repr, DecidableEq

private def natOfDigits (ds : List Char) : Nat :=
  ds.foldl (fun acc c => 10 * acc + (c.toNat - 48)) 0

private def takeDigits (cs : List Char) : List Char × List Char :=
  (cs.takeWhile Char.isDigit, cs.dropWhile Char.isDigit)

/-- Parse an optional `(e|E) [sign] digit+` exponent that consumes the rest. -/
private def parseExp : List Char → Option Int
  | [] => some 0
  | 'e' :: r | 'E' :: r =>
      let (esign, r1) := match r with
        | '-' :: r2 => ((-1 : Int), r2)
        | '+' :: r2 => (1, r2)
        | _ => (1, r)
      let (eds, r2) := takeDigits r1
      if eds = [] ∨ r2 ≠ [] then none else some (esign * (natOfDigits eds : Int))
  | _ => none

/-- Recognize a signed decimal literal spelling and record its base-ten value.
The unsigned part is an MLS 3.7 UNSIGNED-INTEGER or UNSIGNED-REAL, so `2.` and
`.5` are accepted. A malformed spelling (an ordinary identifier, a lone point,
a bare `e`) yields `none`, which resolution reports. -/
def parseDecimal (s : String) : Option Decimal :=
  let cs0 := s.toList
  let (sign, cs1) : Int × List Char := match cs0 with
    | '-' :: r => (-1, r)
    | '+' :: r => (1, r)
    | _ => (1, cs0)
  let (intDs, cs2) := takeDigits cs1
  match cs2 with
  | '.' :: r =>
      let (fracDs, cs3) := takeDigits r
      if intDs = [] ∧ fracDs = [] then none
      else (parseExp cs3).map fun e =>
        ⟨sign, natOfDigits (intDs ++ fracDs), e - (fracDs.length : Int)⟩
  | _ => if intDs = [] then none else (parseExp cs2).map fun e => ⟨sign, natOfDigits intDs, e⟩

/-- Rate magnitude admission: the exact value `|sign| * mantissa * 10 ^ power`
is below `2^969`. Its nearest binary64 value is then below `2^970`, half the
spacing of the largest finite doubles, so adding the rate to any finite double
never overflows. A nonnegative exponent above 330 admits only zero; a negative
exponent is capped at 330, so the check never forms a power of ten beyond
`10^330` and conservatively rejects only literals with more than 600 significant
digits. -/
def Decimal.admitted (d : Decimal) : Bool :=
  let twice := 2 * (d.sign.natAbs * d.mantissa)
  if d.power < 0 then decide (twice < 2 ^ 970 * 10 ^ min (-d.power).toNat 330)
  else twice == 0 || (decide (d.power.toNat ≤ 330) && decide (twice * 10 ^ d.power.toNat < 2 ^ 970))

/-- The fixture literals decode to their exact base-ten content. -/
example : parseDecimal "2.5" = some ⟨1, 25, -1⟩ := by decide
example : parseDecimal "-1" = some ⟨-1, 1, 0⟩ := by decide
example : parseDecimal "x" = none := by decide
example : parseDecimal "2." = some ⟨1, 2, 0⟩ := by decide
example : parseDecimal ".5" = some ⟨1, 5, -1⟩ := by decide
example : parseDecimal "." = none := by decide
example : (parseDecimal "2.5").any Decimal.admitted = true := by decide +kernel
example : (parseDecimal "1e300").any Decimal.admitted = false := by decide +kernel

end Rumoca.ConstantProfile
