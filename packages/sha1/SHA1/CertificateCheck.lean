import SHA1.CertificateProofs
import Lean.Elab.Command

/-! Proof-producing SHA-1 certificates for actual bytes. Named blocks keep
padding and compression checks small. Native evaluation proposes data only;
the kernel checks its connection to the original string and hash definition. -/
namespace SHA1.CertificateCheck
open Lean Elab Command

private def part (name : Name) (kind : String) (index : Nat) : Ident :=
  mkIdent (name.str s!"{kind}_{index}")

private def quoteBytes (bytes : List UInt8) : CommandElabM (TSyntax `term) := do
  let values := bytes.toArray.map fun b => Syntax.mkNumLit (toString b.toNat)
  `(term| ([$values,*] : List UInt8))

private def quoteState (state : State) : CommandElabM (TSyntax `term) := do
  let words := #[state.a, state.b, state.c, state.d, state.e]
    |>.map fun w => Syntax.mkNumLit (toString w.toNat)
  `(term| (State.mk $(words[0]!) $(words[1]!) $(words[2]!) $(words[3]!) $(words[4]!) : State))

/-- Certify the exact UTF-8 bytes, original length and SHA-1 padding. The
resulting named blocks are shared by the compression certificate. -/
def certifyPadding (name : Name) (input : String) : CommandElabM Unit := do
  let bytes := input.toUTF8.data.toList
  let padded := pad bytes
  let count := padded.length / 64
  let full := bytes.length / 64
  let part := part name
  for i in [:count] do
    let block := part "block" i
    let width := part "width" i
    let value ← quoteBytes ((padded.drop (i * 64)).take 64)
    elabCommand (← `(command| def $block:ident : List UInt8 := $value))
    elabCommand (← `(command| theorem $width:ident : ($block).length = 64 := by decide +kernel))
  let last := part "suffix" count
  let lastLength := part "length" count
  elabCommand (← `(command| def $last:ident : List UInt8 := []))
  elabCommand (← `(command| theorem $lastLength:ident : ($last).length = 0 := rfl))
  for j in [:count] do
    let i := count - 1 - j
    let suffix := part "suffix" i
    let rest := part "suffix" (i + 1)
    let block := part "block" i
    let width := part "width" i
    let size := part "length" i
    let restSize := part "length" (i + 1)
    let length := Syntax.mkNumLit (toString ((count - i) * 64))
    elabCommand (← `(command| def $suffix:ident : List UInt8 := $block ++ $rest))
    elabCommand (← `(command| theorem $size:ident : ($suffix).length = $length := by
      change ($block ++ $rest).length = $length
      rw [List.length_append, $width:ident, $restSize:ident]))
  let tail := mkIdent (name.str "padding_tail")
  let tailEq := mkIdent (name.str "padding_tail_eq")
  let originalLength := Syntax.mkNumLit (toString bytes.length)
  let tailValue ← quoteBytes ([128] ++ List.replicate (paddingCount bytes.length) 0 ++ bigEndian (8 * bytes.length) 8)
  elabCommand (← `(command| def $tail:ident : List UInt8 := $tailValue))
  elabCommand (← `(command| theorem $tailEq:ident :
    [128] ++ List.replicate (paddingCount $originalLength) 0 ++ bigEndian (8 * $originalLength) 8 = $tail :=
      by decide +kernel))
  let rawLast := part "raw" full
  let rawLastLength := part "raw_length" full
  let appendLast := part "append" full
  let paddedLast := part "suffix" full
  let rawValue ← quoteBytes (bytes.drop (full * 64))
  let rawSize := Syntax.mkNumLit (toString (bytes.length % 64))
  elabCommand (← `(command| def $rawLast:ident : List UInt8 := $rawValue))
  elabCommand (← `(command| theorem $rawLastLength:ident : ($rawLast).length = $rawSize := by decide +kernel))
  elabCommand (← `(command| theorem $appendLast:ident : $rawLast ++ $tail = $paddedLast := by decide +kernel))
  for j in [:full] do
    let i := full - 1 - j
    let raw := part "raw" i
    let rest := part "raw" (i + 1)
    let size := part "raw_length" i
    let restSize := part "raw_length" (i + 1)
    let block := part "block" i
    let width := part "width" i
    let append := part "append" i
    let restAppend := part "append" (i + 1)
    let suffix := part "suffix" i
    let suffixRest := part "suffix" (i + 1)
    let length := Syntax.mkNumLit (toString (bytes.length - i * 64))
    elabCommand (← `(command| def $raw:ident : List UInt8 := $block ++ $rest))
    elabCommand (← `(command| theorem $size:ident : ($raw).length = $length := by
      change ($block ++ $rest).length = $length
      rw [List.length_append, $width:ident, $restSize:ident]))
    elabCommand (← `(command| theorem $append:ident : $raw ++ $tail = $suffix :=
      Certificate.append_suffix $block $rest $suffixRest $tail $restAppend:ident))
  let source := Syntax.mkStrLit input
  let charsName := mkIdent (name.str "chars")
  let charsEq := mkIdent (name.str "chars_eq")
  let bytesEq := mkIdent (name.str "bytes_eq")
  let chars ← input.toList.toArray.mapM fun c => do
    let n := Syntax.mkNumLit (toString c.toNat)
    `(term| Char.ofNat $n)
  elabCommand (← `(command| def $charsName:ident : List Char := [$chars,*]))
  let raw := part "raw" 0
  let rawLength := part "raw_length" 0
  let append := part "append" 0
  let allBytes := part "suffix" 0
  let allLength := part "length" 0
  let paddingName := mkIdent (name.str "padding")
  let sizeName := mkIdent (name.str "size")
  let countSyntax := Syntax.mkNumLit (toString count)
  -- Guide elaboration only; the kernel still checks every literal equality.
  elabCommand (← `(command| section))
  try
    elabCommand (← `(command| attribute [local irreducible] String.ofList))
    elabCommand (← `(command| theorem $charsEq:ident : $source = String.ofList $charsName := by rfl))
    elabCommand (← `(command| theorem $bytesEq:ident : ($source).toUTF8.data.toList = $raw :=
      (Certificate.utf8_of_chars $source $charsName $charsEq:ident).trans (by decide +kernel)))
    elabCommand (← `(command| theorem $paddingName:ident : pad ($source).toUTF8.data.toList = $allBytes :=
      (congrArg pad $bytesEq:ident).trans
        ((Certificate.pad_of_length $raw $tail $originalLength $rawLength:ident $tailEq:ident).trans $append:ident)))
  finally
    elabCommand (← `(command| end))
  elabCommand (← `(command| theorem $sizeName:ident : ($allBytes).length / 64 = $countSyntax :=
    (congrArg (· / 64) $allLength:ident).trans (by decide +kernel)))

/-- Produce a theorem for precisely `hash input.toUTF8 = candidateDigest`.
The caller supplies a fresh theorem name and audits its complete dependencies. -/
def certify (name : Name) (input : String) : CommandElabM Unit := do
  certifyPadding name input
  if (← get).messages.hasErrors then
    throwError "SHA-1 padding certificate failed"
  let padded := pad input.toUTF8.data.toList
  let count := padded.length / 64
  let part := part name
  let mut state := initial
  let start ← quoteState state
  let stateName := part "state" 0
  elabCommand (← `(command| def $stateName:ident : State := $start))
  for i in [:count] do
    let block := part "block" i
    let before := part "state" i
    let after := part "state" (i + 1)
    let step := part "step" i
    state := compress state ((padded.drop (i * 64)).take 64)
    let value ← quoteState state
    elabCommand (← `(command| def $after:ident : State := $value))
    elabCommand (← `(command| theorem $step:ident : compress $before $block = $after := by decide +kernel))
  let last := part "suffix" count
  let finalState := part "state" count
  let lastRun := part "run" count
  elabCommand (← `(command| theorem $lastRun:ident :
    foldBlocksUsing compress 0 $last $finalState = $finalState := rfl))
  for j in [:count] do
    let i := count - 1 - j
    let suffix := part "suffix" i
    let rest := part "suffix" (i + 1)
    let block := part "block" i
    let before := part "state" i
    let after := part "state" (i + 1)
    let width := part "width" i
    let step := part "step" i
    let tailRun := part "run" (i + 1)
    let run := part "run" i
    let remaining := Syntax.mkNumLit (toString (count - i))
    elabCommand (← `(command| theorem $run:ident :
      foldBlocksUsing compress $remaining $suffix $before = $finalState :=
        Certificate.block_cons compress _ $block $rest $before $after $finalState
          $width:ident $step:ident $tailRun:ident))
  let bytes := Syntax.mkStrLit input
  let digest := Syntax.mkStrLit (hash input.toUTF8)
  let allBytes := part "suffix" 0
  let allRun := part "run" 0
  let paddingName := mkIdent (name.str "padding")
  let sizeName := mkIdent (name.str "size")
  let countSyntax := Syntax.mkNumLit (toString count)
  let theoremId := mkIdent name
  elabCommand (← `(command| theorem $theoremId:ident : hash ($bytes).toUTF8 = $digest := by
    exact (Certificate.hash_of_blocks ($bytes).toUTF8 $allBytes $countSyntax $finalState
      $paddingName:ident $sizeName:ident $allRun:ident).trans (by decide +kernel)))
  if (← get).messages.hasErrors then
    throwError "SHA-1 compression certificate failed"

end SHA1.CertificateCheck
