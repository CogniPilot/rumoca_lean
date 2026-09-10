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
  let cleaned := String.ofList (strip (source.toList.length + 1) false source.toList)
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
