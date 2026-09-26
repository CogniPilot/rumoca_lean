import Parser.LALR.Runtime

/-! Source position of a syntax rejection. -/
namespace Parser.LALR

/-- The number of input symbols not yet consumed when `run` stops without a
tree. Frontends use it only to place a syntax diagnostic at the offending
token; it neither recovers from the error nor changes any parse result. -/
def unconsumed (g : Grammar) (tables : Tables) : Nat → Configuration → Nat
  | 0, c => c.remaining.length
  | fuel + 1, c =>
    match step g tables c with
    | .next next => unconsumed g tables fuel next
    | .accepted _ => 0
    | .failed _ => c.remaining.length

end Parser.LALR
