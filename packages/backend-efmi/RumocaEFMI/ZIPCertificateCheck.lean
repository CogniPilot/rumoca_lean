import RumocaEFMI.ZIPCertificate
import Lean.Elab.Command

/-! Candidate byte/CRC traces with bounded kernel proofs. Native evaluation
selects literals and intermediate CRC states; no native result authorizes the
certificate. Every character encoding, byte transition and composition is
checked by Lean. -/
namespace Rumoca.EFMI.StoredZIP.CertificateCheck
open Lean Elab Command

private def part (name : Name) (kind : String) (index : Nat) : Ident :=
  mkIdent (name.str s!"{kind}_{index}")

def quoteBytes (bytes : List UInt8) : CommandElabM (TSyntax `term) := do
  let values := bytes.toArray.map fun b => Syntax.mkNumLit (toString b.toNat)
  `(term| ([$values,*] : List UInt8))

/-- The `bytes_0` definition is the exact UTF-8 byte list, represented by
bounded blocks. `utf8` and `length_0` certify its connection and size. -/
def certifyUTF8 (name : Name) (input : String) : CommandElabM (Array (List UInt8)) := do
  let chars := input.toList.toArray
  let count := (chars.size + 63) / 64
  let mut blocks := #[]
  for i in [:count] do
    let chunk := (chars.extract (64 * i) (64 * (i + 1))).toList
    let bytes := chunk.flatMap String.utf8EncodeChar
    blocks := blocks.push bytes
    let charsName := part name "char_block" i
    let bytesName := part name "byte_block" i
    let eq := part name "encoded" i
    let length := part name "width" i
    let quoted ← chunk.toArray.mapM fun c => do
      let n := Syntax.mkNumLit (toString c.toNat)
      `(term| Char.ofNat $n)
    let raw ← quoteBytes bytes
    let size := Syntax.mkNumLit (toString bytes.length)
    elabCommand (← `(command| def $charsName:ident : List Char := [$quoted,*]))
    elabCommand (← `(command| def $bytesName:ident : List UInt8 := $raw))
    elabCommand (← `(command| theorem $eq:ident :
      ($charsName).flatMap String.utf8EncodeChar = $bytesName := by decide +kernel))
    elabCommand (← `(command| theorem $length:ident : ($bytesName).length = $size := by decide +kernel))
  let charsEnd := part name "chars" count
  let bytesEnd := part name "bytes" count
  let encodedEnd := part name "utf8_tail" count
  let sizeEnd := part name "length" count
  elabCommand (← `(command| def $charsEnd:ident : List Char := []))
  elabCommand (← `(command| def $bytesEnd:ident : List UInt8 := []))
  elabCommand (← `(command| theorem $encodedEnd:ident :
    ($charsEnd).flatMap String.utf8EncodeChar = $bytesEnd := rfl))
  elabCommand (← `(command| theorem $sizeEnd:ident : ($bytesEnd).length = 0 := rfl))
  let mut length := 0
  for j in [:count] do
    let i := count - 1 - j
    let chars := part name "chars" i
    let raw := part name "bytes" i
    let tailChars := part name "chars" (i + 1)
    let tailRaw := part name "bytes" (i + 1)
    let headChars := part name "char_block" i
    let headRaw := part name "byte_block" i
    let headEq := part name "encoded" i
    let tailEq := part name "utf8_tail" (i + 1)
    let eq := part name "utf8_tail" i
    let size := part name "length" i
    let width := part name "width" i
    let tailSize := part name "length" (i + 1)
    length := length + blocks[i]!.length
    let n := Syntax.mkNumLit (toString length)
    elabCommand (← `(command| def $chars:ident : List Char := $headChars ++ $tailChars))
    elabCommand (← `(command| def $raw:ident : List UInt8 := $headRaw ++ $tailRaw))
    elabCommand (← `(command| theorem $eq:ident : ($chars).flatMap String.utf8EncodeChar = $raw :=
      Certificate.encode_cons $headChars $tailChars $headRaw $tailRaw $headEq:ident $tailEq:ident))
    elabCommand (← `(command| theorem $size:ident : ($raw).length = $n := by
      change ($headRaw ++ $tailRaw).length = $n
      rw [List.length_append, $width:ident, $tailSize:ident]))
  let source := Syntax.mkStrLit input
  let chars := part name "chars" 0
  let bytes := part name "bytes" 0
  let tailEq := part name "utf8_tail" 0
  let sourceEq := mkIdent (name.str "source_eq")
  let utf8 := mkIdent (name.str "utf8")
  elabCommand (← `(command| section))
  try
    elabCommand (← `(command| attribute [local irreducible] String.ofList))
    elabCommand (← `(command| theorem $sourceEq:ident : $source = String.ofList $chars := by rfl))
    elabCommand (← `(command| theorem $utf8:ident : ($source).toUTF8.data.toList = $bytes :=
      (Certificate.utf8_of_chars $source $chars $sourceEq:ident).trans $tailEq:ident))
  finally elabCommand (← `(command| end))
  if (← get).messages.hasErrors then throwError "ZIP UTF-8 certificate failed"
  return blocks

/-- Certify CRC-32 for the exact input string. Blocks preserve the original
byte order, and the kernel checks each intermediate state. -/
def certifyCRC (name : Name) (input : String) : CommandElabM Unit := do
  let blocks ← certifyUTF8 name input
  let mut state : UInt32 := 0xffffffff
  for i in [:blocks.size] do
    let before := Syntax.mkNumLit (toString state.toNat)
    state := blocks[i]!.foldl CRC32.byte state
    let after := Syntax.mkNumLit (toString state.toNat)
    let step := part name "crc_step" i
    let head := part name "byte_block" i
    elabCommand (← `(command| theorem $step:ident :
      ($head).foldl CRC32.byte $before = $after := by decide +kernel))
  let result := Syntax.mkNumLit (toString state.toNat)
  let endRun := part name "crc_run" blocks.size
  let endBytes := part name "bytes" blocks.size
  elabCommand (← `(command| theorem $endRun:ident :
    ($endBytes).foldl CRC32.byte $result = $result := rfl))
  let states := blocks.foldl (fun states bytes => states.push (bytes.foldl CRC32.byte states.back!)) #[0xffffffff]
  for j in [:blocks.size] do
    let i := blocks.size - 1 - j
    let bytes := part name "bytes" i
    let head := part name "byte_block" i
    let tail := part name "bytes" (i + 1)
    let step := part name "crc_step" i
    let run := part name "crc_run" i
    let rest := part name "crc_run" (i + 1)
    let before := Syntax.mkNumLit (toString states[i]!.toNat)
    let after := Syntax.mkNumLit (toString states[i + 1]!.toNat)
    elabCommand (← `(command| theorem $run:ident : ($bytes).foldl CRC32.byte $before = $result :=
      Certificate.crc_cons $head $tail $before $after $result $step:ident $rest:ident))
  let source := Syntax.mkStrLit input
  let bytes := part name "bytes" 0
  let utf8 := mkIdent (name.str "utf8")
  let run := part name "crc_run" 0
  let crc := mkIdent (name.str "crc")
  let value := Syntax.mkNumLit (toString (state ^^^ 0xffffffff).toNat)
  elabCommand (← `(command| theorem $crc:ident : CRC32.checksum ($source).toUTF8 = $value :=
    (Certificate.crc_of_bytes ($source).toUTF8 $bytes $result $utf8:ident $run:ident).trans
      (by decide +kernel)))
  let payload := mkIdent (name.str "payload")
  let length := part name "length" 0
  let size := Syntax.mkNumLit (toString input.toUTF8.size)
  elabCommand (← `(command| def $payload:ident : Certificate.Text :=
    ⟨$source, $bytes, $size, $value, $utf8:ident, $length:ident, $crc:ident⟩))
  if (← get).messages.hasErrors then throwError "ZIP CRC certificate failed"

end Rumoca.EFMI.StoredZIP.CertificateCheck
