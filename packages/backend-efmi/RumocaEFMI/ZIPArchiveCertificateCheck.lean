import RumocaEFMI.ZIPArchiveCertificate
import RumocaEFMI.ZIPCertificateCheck

/-! Fixed byte-to-proposition adapter for stored ZIP archives. Each quoted
segment is taken from the actual input at a monotonically advancing cursor;
the final segment contains the entire remainder. Expected sizes only choose
segment boundaries. They never supply archive bytes. Bounded equalities are
checked by the kernel and composed into the complete `Format.Conforms` claim.
The caller must bind the resulting entry list to its semantic contract. -/
namespace Rumoca.EFMI.StoredZIP.ArchiveCertificateCheck
open Lean Elab Command

structure Candidate where
  name : String
  text : String
  certificate : Name
  deriving Inhabited

private def part (name : Name) (kind : String) (index : Nat) : Ident :=
  mkIdent (name.str s!"{kind}_{index}")

private def numeral (n : Nat) : TSyntax `num := Syntax.mkNumLit (toString n)

private def certifyCore (name : Name) (input : ByteArray) (items : Array Candidate) : CommandElabM Unit := do
  let mut cursor := 0
  let mut offsets := #[0]
  let mut centralSize := 0
  for i in [:items.size] do
    let item := items[i]!
    let text := mkIdent (item.certificate.str "payload")
    let entry := part name "entry" i
    let entryName := Syntax.mkStrLit item.name
    let source := Syntax.mkStrLit item.text
    elabCommand (← `(command| def $entry:ident : Entry := ⟨$entryName, ($source).toUTF8⟩))
    let header := part name "header" i
    let headerSize := 30 + item.name.toUTF8.size
    let actualHeader := input.extract cursor (cursor + headerSize)
    cursor := cursor + actualHeader.size
    let quoted ← CertificateCheck.quoteBytes actualHeader.data.toList
    elabCommand (← `(command| def $header:ident : List UInt8 := $quoted))
    let chars := item.text.toList.toArray
    let count := (chars.size + 63) / 64
    for j in [:count] do
      let width := ((chars.extract (64*j) (64*(j+1))).toList.flatMap String.utf8EncodeChar).length
      let actual := input.extract cursor (cursor + width)
      cursor := cursor + actual.size
      let block := part (name.str s!"payload_{i}") "block" j
      let expected := part item.certificate "byte_block" j
      let eq := part (name.str s!"payload_{i}") "block_eq" j
      let quoted ← CertificateCheck.quoteBytes actual.data.toList
      elabCommand (← `(command| def $block:ident : List UInt8 := $quoted))
      elabCommand (← `(command| theorem $eq:ident : $block = $expected := by decide +kernel))
    let payloadEnd := part (name.str s!"payload_{i}") "bytes" count
    let payloadEndEq := part (name.str s!"payload_{i}") "eq" count
    let expectedEnd := part item.certificate "bytes" count
    elabCommand (← `(command| def $payloadEnd:ident : List UInt8 := []))
    elabCommand (← `(command| theorem $payloadEndEq:ident : $payloadEnd = $expectedEnd := rfl))
    for j in [:count] do
      let k := count - 1 - j
      let block := part (name.str s!"payload_{i}") "block" k
      let tail := part (name.str s!"payload_{i}") "bytes" (k+1)
      let bytes := part (name.str s!"payload_{i}") "bytes" k
      let expected := part item.certificate "bytes" k
      let headEq := part (name.str s!"payload_{i}") "block_eq" k
      let tailEq := part (name.str s!"payload_{i}") "eq" (k+1)
      let eq := part (name.str s!"payload_{i}") "eq" k
      elabCommand (← `(command| def $bytes:ident : List UInt8 := $block ++ $tail))
      elabCommand (← `(command| theorem $eq:ident : $bytes = $expected :=
        Certificate.append_equal _ _ _ _ $headEq:ident $tailEq:ident))
    let payload := part (name.str s!"payload_{i}") "bytes" 0
    let payloadEq := part (name.str s!"payload_{i}") "eq" 0
    let payloadLength := part item.certificate "length" 0
    let record := part name "local" i
    let recordEq := part name "local_eq" i
    let recordSize := part name "local_size" i
    let fits := part name "fits" i
    let nameBytes ← CertificateCheck.quoteBytes item.name.toUTF8.data.toList
    let headerEq := part name "header_eq" i
    let totalSize := numeral (headerSize + item.text.toUTF8.size)
    elabCommand (← `(command| def $record:ident : List UInt8 := $header ++ $payload))
    elabCommand (← `(command| theorem $headerEq:ident :
      Certificate.localPrefix ($text).crc.toNat ($text).size $nameBytes = $header := by decide +kernel))
    if (← get).messages.hasErrors then throwError "ZIP local header certificate failed: {item.name}"
    elabCommand (← `(command| theorem $recordEq:ident : Format.localRecord $entry = $record :=
      (Certificate.localRecord_parts $entry $nameBytes ($text).bytes ($text).crc ($text).size
        (by decide +kernel) ($text).encoding ($text).checksum ($text).length).trans
          (Certificate.append_equal _ _ _ _ $headerEq:ident ($payloadEq:ident).symm)))
    if (← get).messages.hasErrors then throwError "ZIP local record composition failed: {item.name}"
    elabCommand (← `(command| theorem $recordSize:ident : ($record).length = $totalSize := by
      change ($header ++ $payload).length = $totalSize
      rw [List.length_append, $payloadEq:ident, $payloadLength:ident]
      decide +kernel))
    if (← get).messages.hasErrors then throwError "ZIP local length certificate failed: {item.name}"
    elabCommand (← `(command| theorem $fits:ident : Format.entryFits $entry = true :=
      Certificate.Text.entryFits $text $entryName
        (by simp +decide [safeName, String.splitOn, String.splitOnAux])
        (by decide +kernel) (by decide +kernel)))
    offsets := offsets.push (offsets.back! + headerSize + item.text.toUTF8.size)
    if (← get).messages.hasErrors then throwError "ZIP local member certificate failed: {item.name}"
  for i in [:items.size] do
    let item := items[i]!
    let text := mkIdent (item.certificate.str "payload")
    let entry := part name "entry" i
    let central := part name "central" i
    let eq := part name "central_eq" i
    let sizeEq := part name "central_size" i
    let nameBytes ← CertificateCheck.quoteBytes item.name.toUTF8.data.toList
    let size := 46 + item.name.toUTF8.size
    let actual := input.extract cursor (cursor + size)
    cursor := cursor + actual.size
    centralSize := centralSize + size
    let quoted ← CertificateCheck.quoteBytes actual.data.toList
    let offset := numeral offsets[i]!
    let width := numeral size
    elabCommand (← `(command| def $central:ident : List UInt8 := $quoted))
    elabCommand (← `(command| theorem $eq:ident : Format.centralRecord $offset $entry = $central :=
      (Certificate.centralRecord_parts $entry $nameBytes ($text).bytes ($text).crc $offset ($text).size
        (by decide +kernel) ($text).encoding ($text).checksum ($text).length).trans
          (by decide +kernel)))
    elabCommand (← `(command| theorem $sizeEq:ident : ($central).length = $width := by decide +kernel))
    if (← get).messages.hasErrors then throwError "ZIP central member certificate failed: {item.name}"
  let ending := mkIdent (name.str "ending")
  let remaining := input.extract cursor input.size
  let quoted ← CertificateCheck.quoteBytes remaining.data.toList
  elabCommand (← `(command| def $ending:ident : List UInt8 := $quoted))
  let count := items.size
  let entriesEnd := part name "entries" count
  let localsEnd := part name "locals" count
  let centralEnd := part name "directory" count
  let localEqEnd := part name "locals_eq" count
  let centralEqEnd := part name "directory_eq" count
  let fitsEnd := part name "all_fit" count
  let localSizeEnd := part name "locals_size" count
  let centralSizeEnd := part name "directory_size" count
  let endOffset := numeral offsets.back!
  elabCommand (← `(command| def $entriesEnd:ident : List Entry := []))
  elabCommand (← `(command| def $localsEnd:ident : List UInt8 := []))
  elabCommand (← `(command| def $centralEnd:ident : List UInt8 := []))
  elabCommand (← `(command| theorem $localEqEnd:ident : Format.localRecords $entriesEnd = $localsEnd := rfl))
  elabCommand (← `(command| theorem $centralEqEnd:ident : Format.directory $endOffset $entriesEnd = $centralEnd := rfl))
  elabCommand (← `(command| theorem $fitsEnd:ident : ($entriesEnd).all Format.entryFits = true := rfl))
  elabCommand (← `(command| theorem $localSizeEnd:ident : ($localsEnd).length = 0 := rfl))
  elabCommand (← `(command| theorem $centralSizeEnd:ident : ($centralEnd).length = 0 := rfl))
  let mut remainingCentral := 0
  for j in [:count] do
    let i := count - 1 - j
    let entry := part name "entry" i
    let entries := part name "entries" i
    let tailEntries := part name "entries" (i+1)
    let localHead := part name "local" i
    let localTail := part name "locals" (i+1)
    let locals := part name "locals" i
    let centralHead := part name "central" i
    let centralTail := part name "directory" (i+1)
    let central := part name "directory" i
    let localHeadEq := part name "local_eq" i
    let localTailEq := part name "locals_eq" (i+1)
    let localEq := part name "locals_eq" i
    let centralHeadEq := part name "central_eq" i
    let centralTailEq := part name "directory_eq" (i+1)
    let centralEq := part name "directory_eq" i
    let localHeadSize := part name "local_size" i
    let localTailSize := part name "locals_size" (i+1)
    let localSize := part name "locals_size" i
    let centralHeadSize := part name "central_size" i
    let centralTailSize := part name "directory_size" (i+1)
    let centralSizeEq := part name "directory_size" i
    let headFit := part name "fits" i
    let tailFit := part name "all_fit" (i+1)
    let fits := part name "all_fit" i
    let offset := numeral offsets[i]!
    let next := numeral offsets[i+1]!
    let localLength := numeral (offsets.back! - offsets[i]!)
    remainingCentral := remainingCentral + 46 + items[i]!.name.toUTF8.size
    let centralLength := numeral remainingCentral
    elabCommand (← `(command| def $entries:ident : List Entry := $entry :: $tailEntries))
    elabCommand (← `(command| def $locals:ident : List UInt8 := $localHead ++ $localTail))
    elabCommand (← `(command| def $central:ident : List UInt8 := $centralHead ++ $centralTail))
    elabCommand (← `(command| theorem $localEq:ident : Format.localRecords $entries = $locals :=
      Certificate.local_cons _ _ _ _ $localHeadEq:ident $localTailEq:ident))
    elabCommand (← `(command| theorem $centralEq:ident : Format.directory $offset $entries = $central :=
      Certificate.directory_cons _ _ $offset $next _ _ $centralHeadEq:ident
        (by rw [$localHeadEq:ident, $localHeadSize:ident]) $centralTailEq:ident))
    elabCommand (← `(command| theorem $fits:ident : ($entries).all Format.entryFits = true :=
      Certificate.entry_fits_cons _ _ $headFit:ident $tailFit:ident))
    elabCommand (← `(command| theorem $localSize:ident : ($locals).length = $localLength :=
      Certificate.append_length _ _ _ _ $localHeadSize:ident $localTailSize:ident))
    elabCommand (← `(command| theorem $centralSizeEq:ident : ($central).length = $centralLength :=
      Certificate.append_length _ _ _ _ $centralHeadSize:ident $centralTailSize:ident))
  let entries := part name "entries" 0
  let locals := part name "locals" 0
  let central := part name "directory" 0
  let localEq := part name "locals_eq" 0
  let centralEq := part name "directory_eq" 0
  let fits := part name "all_fit" 0
  let localSize := part name "locals_size" 0
  let centralSizeEq := part name "directory_size" 0
  let localLength := numeral offsets.back!
  let centralLength := numeral centralSize
  let bytes := mkIdent (name.str "bytes")
  let conforms := mkIdent (name.str "conforms")
  elabCommand (← `(command| def $bytes:ident : ByteArray := ⟨($locals ++ $central ++ $ending).toArray⟩))
  elabCommand (← `(command| theorem $conforms:ident : Format.Conforms $entries $bytes :=
    Certificate.archive $entries $bytes $locals $central $ending $localLength $centralLength
      (by decide +kernel) (by decide +kernel) $fits:ident $localEq:ident $centralEq:ident
      $localSize:ident $centralSizeEq:ident (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by simp only [$bytes:ident, List.toList_toArray])))
  if (← get).messages.hasErrors then throwError "ZIP archive certificate failed"

/-- Produces `entries_0`, the literal-backed `bytes`, and a kernel-checked
`conforms` theorem. Payload certificates must already be available. Keep the
record and encoding functions symbolic during elaborator unification so it
uses the supplied facts instead of expanding complete payloads. The kernel
still checks every proof and all bounded computational equalities. -/
def certify (name : Name) (input : ByteArray) (items : Array Candidate) : CommandElabM Unit := do
  elabCommand (← `(command| section))
  try
    elabCommand (← `(command| attribute [local irreducible]
      Format.localRecord Format.centralRecord CRC32.checksum String.toUTF8))
    certifyCore name input items
  finally elabCommand (← `(command| end))

end Rumoca.EFMI.StoredZIP.ArchiveCertificateCheck
