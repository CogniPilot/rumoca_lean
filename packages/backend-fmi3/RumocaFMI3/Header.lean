import RumocaC.Tree

/-! Read function signatures from the official pinned FMI header. This is
build-time tooling, not an FMI implementation or a trusted proof procedure.
Compiling definitions against fmi3Functions.h independently checks the ABI. -/
namespace Rumoca.FMI3.Header
open CTree

private def strip (fuel : Nat) (block : Bool) (cs : List Char) : List Char :=
  match fuel, block, cs with
  | 0, _, _ | _, _, [] => []
  | f + 1, false, '/' :: '*' :: rest => ' ' :: strip f true rest
  | f + 1, true, '*' :: '/' :: rest => ' ' :: strip f false rest
  | f + 1, true, _ :: rest => strip f true rest
  | f + 1, false, c :: rest => c :: strip f false rest

private def stripInto (fuel : Nat) (block : Bool) (cs acc : List Char) : List Char :=
  match fuel, block, cs with
  | 0, _, _ | _, _, [] => acc.reverse
  | f + 1, false, '/' :: '*' :: rest => stripInto f true rest (' ' :: acc)
  | f + 1, true, '*' :: '/' :: rest => stripInto f false rest (' ' :: acc)
  | f + 1, true, _ :: rest => stripInto f true rest acc
  | f + 1, false, c :: rest => stripInto f false rest (c :: acc)

private theorem stripInto_eq (fuel : Nat) (block : Bool) (cs acc : List Char) :
    stripInto fuel block cs acc = acc.reverse ++ strip fuel block cs := by
  induction fuel generalizing block cs acc with
  | zero => simp [stripInto, strip]
  | succ fuel ih =>
    cases block <;> cases cs with
    | nil => simp [stripInto, strip]
    | cons c cs =>
      cases cs with
      | nil => simp [stripInto, strip, List.reverse_cons, List.append_assoc, ih]
      | cons d ds =>
        by_cases slash : c = '/' <;> by_cases star : c = '*' <;>
          by_cases nextSlash : d = '/' <;> by_cases nextStar : d = '*' <;>
          simp_all [stripInto, strip, List.reverse_cons, List.append_assoc]

/-- Accumulator-based comment removal avoids interpreter recursion proportional
to the header length. It preserves the existing restricted reader exactly. -/
def commentText (source : String) : String :=
  String.ofList (stripInto (source.toList.length + 1) false source.toList [])

theorem commentText_reference (source : String) :
    commentText source = String.ofList (strip (source.toList.length + 1) false source.toList) := by
  simp [commentText, stripInto_eq]

private def tokens (s : String) : List String :=
  (String.join (s.toList.map fun c =>
    if c.isWhitespace then " " else if ['(', ')', '*', '[', ']', ','].contains c
    then " " ++ String.singleton c ++ " " else String.singleton c)).splitOn " " |>.filter (· != "")

private def parameter (ts : List String) : Except String Parameter := do
  let array := ts.reverse.take 2 == ["]", "["]
  let ts := if array then ts.dropLast.dropLast else ts
  let some name := ts.getLast? | throw "empty FMI parameter"
  if ts.length < 2 then throw s!"invalid FMI parameter: {ts}"
  return ⟨String.intercalate " " ts.dropLast, name, array⟩

private def splitComma (ts : List String) : List (List String) :=
  (String.intercalate " " ts).splitOn "," |>.map fun s => (tokens s)

def signatures (source : String) : Except String (List Signature) := do
  let cleaned := commentText source
  let mut result := []
  for declaration in cleaned.splitOn ";" do
    let chunks := declaration.splitOn "typedef"
    if chunks.length < 2 then continue
    let ts := tokens (chunks.getLast?.getD "")
    let headTokens := ts.takeWhile (· != "(")
    let some name := headTokens.getLast? | continue
    if !name.startsWith "fmi3" || !name.endsWith "TYPE" then continue
    let name := (name.dropEnd 4).toString
    let args := (ts.drop (headTokens.length + 1)).takeWhile (· != ")")
    let params ← if args == ["void"] then pure [] else (splitComma args).mapM parameter
    if result.any (fun s : Signature => s.name == name) then throw s!"duplicate FMI function {name}"
    result := result ++ [⟨String.intercalate " " headTokens.dropLast, name, params⟩]
  if result.length < 50 then throw "FMI header contains too few function declarations"
  return result

end Rumoca.FMI3.Header
