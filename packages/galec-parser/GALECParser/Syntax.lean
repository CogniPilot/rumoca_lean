import Parser.Scanner

open _root_.Parser

/-! GALEC lexical policy. Words are classified into reserved words and names;
digit-initial runs are `Token.number`, whose grammar symbol is `IDENT`, so a
number never becomes a name token. Method names are ordinary names. GALEC
comments, quoted names, exponents and signed numerals are not scanned. The
obsolete pointwise `.*` spelling has no token: `.` and `*` are separate
symbols, so that spelling is rejected by the grammar. -/
namespace Rumoca.GALEC.Syntax

def reserved : List String :=
  ["block", "output", "Real", "protected", "constant", "public", "method", "algorithm",
   "self", "end", "input", "parameter", "function", "record", "signals", "Boolean",
   "Integer", "limit", "if", "signal", "in", "then", "elseif", "else", "for", "loop",
   "and", "or", "not", "size", "while", "do", "until", "break", "return",
   "enumeration", "true", "false"]

def scanner : Scanner.Config where
  wordStart := asciiLetter
  wordRest := identRest
  numberRest := fun c => c.isDigit || c == '.'
  classify := fun word => if reserved.contains word then .literal word else .ident word
  number := .number
  single := fun c => [';', '.', '+', '*', ':', '(', ')', '[', ']', ','].contains c
  pair := fun c => if c == ':' then some '=' else none

end Rumoca.GALEC.Syntax
