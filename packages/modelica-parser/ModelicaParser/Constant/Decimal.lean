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
A malformed spelling (an ordinary identifier, a trailing point, a bare `e`)
yields `none`, which resolution reports. -/
def parseDecimal (s : String) : Option Decimal :=
  let cs0 := s.toList
  let (sign, cs1) : Int × List Char := match cs0 with
    | '-' :: r => (-1, r)
    | '+' :: r => (1, r)
    | _ => (1, cs0)
  let (intDs, cs2) := takeDigits cs1
  if intDs = [] then none
  else match cs2 with
    | '.' :: r =>
        let (fracDs, cs3) := takeDigits r
        if fracDs = [] then none
        else (parseExp cs3).map fun e =>
          ⟨sign, natOfDigits (intDs ++ fracDs), e - (fracDs.length : Int)⟩
    | _ => (parseExp cs2).map fun e => ⟨sign, natOfDigits intDs, e⟩

/-- The fixture literals decode to their exact base-ten content. -/
example : parseDecimal "2.5" = some ⟨1, 25, -1⟩ := by decide
example : parseDecimal "-1" = some ⟨-1, 1, 0⟩ := by decide
example : parseDecimal "x" = none := by decide

end Rumoca.ConstantProfile
