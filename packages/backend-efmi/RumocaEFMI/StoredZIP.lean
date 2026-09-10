import RumocaEFMI.ZIPFormat

/-! A deliberately narrow ZIP32 transport: stored regular files, ASCII relative
names, no encryption, extra fields, comments, descriptors or multi-disk data.
The independent reader checks local records, central records, offsets, sizes,
CRCs and the complete end record. It never extracts paths to the filesystem.
This module is under E05 development; no eFMU publication path uses it yet. -/
namespace Rumoca.EFMI.StoredZIP

def littleEndian (value count : Nat) : ByteArray :=
  ((List.range count).map fun i => (value >>> (8 * i)).toUInt8).toByteArray

/-- Pairs are (byte width, unsigned value), in wire order. -/
def fields (values : List (Nat × Nat)) : ByteArray :=
  values.foldl (fun out (width, value) => out ++ littleEndian value width) ByteArray.empty

def localHeader (entry : Entry) (crc : UInt32) : ByteArray := fields
  [(4, 0x04034b50), (2, 10), (2, 0), (2, 0), (2, 0), (2, 33),
   (4, crc.toNat), (4, entry.bytes.size), (4, entry.bytes.size),
   (2, entry.name.toUTF8.size), (2, 0)] ++ entry.name.toUTF8

def centralHeader (entry : Entry) (crc : UInt32) (offset : Nat) : ByteArray := fields
  [(4, 0x02014b50), (2, 20), (2, 10), (2, 0), (2, 0), (2, 0), (2, 33),
   (4, crc.toNat), (4, entry.bytes.size), (4, entry.bytes.size),
   (2, entry.name.toUTF8.size), (2, 0), (2, 0), (2, 0), (2, 0), (4, 0), (4, offset)] ++
    entry.name.toUTF8

def endRecord (count size offset : Nat) : ByteArray := fields
  [(4, 0x06054b50), (2, 0), (2, 0), (2, count), (2, count), (4, size), (4, offset), (2, 0)]

def guard (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

def writeRecords : List Entry → ByteArray → ByteArray → Except String (ByteArray × ByteArray)
  | [], localBytes, central => .ok (localBytes, central)
  | entry :: rest, localBytes, central => do
    guard (Format.entryFits entry) "unsafe ZIP member name or ZIP32 member size exceeded"
    let crc := CRC32.checksum entry.bytes
    let central := central ++ centralHeader entry crc localBytes.size
    let localBytes := localBytes ++ (localHeader entry crc ++ entry.bytes)
    guard (localBytes.size < 2^32 && central.size < 2^32) "ZIP32 archive size exceeded"
    writeRecords rest localBytes central

def encode (entries : List Entry) : Except String ByteArray := do
  guard (entries.length < 65536) "ZIP32 entry count exceeded"
  guard (decide (entries.map Entry.name).Nodup) "duplicate ZIP member"
  let (localBytes, central) ← writeRecords entries ByteArray.empty ByteArray.empty
  return localBytes ++ central ++ endRecord entries.length central.size localBytes.size

structure Cursor where
  bytes : ByteArray
  position : Nat := 0

def readBytes (count : Nat) (cursor : Cursor) : Except String (ByteArray × Cursor) := do
  guard (cursor.position + count ≤ cursor.bytes.size) "truncated ZIP record"
  return (cursor.bytes.extract cursor.position (cursor.position + count),
    { cursor with position := cursor.position + count })

def readNumber (count : Nat) (cursor : Cursor) : Except String (Nat × Cursor) := do
  let (bytes, cursor) ← readBytes count cursor
  let value := bytes.data.toList.foldr (fun b rest => b.toNat + 256 * rest) 0
  return (value, cursor)

def expect (width wanted : Nat) (cursor : Cursor) : Except String Cursor := do
  let (value, cursor) ← readNumber width cursor
  guard (value == wanted) "unsupported or inconsistent ZIP header"
  return cursor

def expectFields (values : List (Nat × Nat)) (cursor : Cursor) : Except String Cursor :=
  values.foldlM (fun cursor (width, value) => expect width value cursor) cursor

structure Local where
  entry : Entry
  offset : Nat
  crc : Nat

def readLocal (cursor : Cursor) : Except String (Local × Cursor) := do
  let offset := cursor.position
  let cursor ← expectFields [(4, 0x04034b50), (2, 10), (2, 0), (2, 0), (2, 0), (2, 33)] cursor
  let (crc, cursor) ← readNumber 4 cursor
  let (size, cursor) ← readNumber 4 cursor
  let cursor ← expect 4 size cursor
  let (nameLength, cursor) ← readNumber 2 cursor
  let cursor ← expect 2 0 cursor
  let (nameBytes, cursor) ← readBytes nameLength cursor
  let some name := String.fromUTF8? nameBytes | throw "invalid ZIP name encoding"
  guard (safeName name) "unsafe ZIP member name"
  let (data, cursor) ← readBytes size cursor
  guard ((CRC32.checksum data).toNat == crc) "ZIP member CRC mismatch"
  return (⟨⟨name, data⟩, offset, crc⟩, cursor)

def readLocals : Nat → Cursor → Except String (List Local × Cursor)
  | 0, cursor => .ok ([], cursor)
  | count + 1, cursor => do
    let (record, cursor) ← readLocal cursor
    let (rest, cursor) ← readLocals count cursor
    return (record :: rest, cursor)

def checkCentral (record : Local) (cursor : Cursor) : Except String Cursor := do
  let entry := record.entry
  let cursor ← expectFields
    [(4, 0x02014b50), (2, 20), (2, 10), (2, 0), (2, 0), (2, 0), (2, 33),
     (4, record.crc), (4, entry.bytes.size), (4, entry.bytes.size),
     (2, entry.name.toUTF8.size), (2, 0), (2, 0), (2, 0), (2, 0), (4, 0), (4, record.offset)] cursor
  let (name, cursor) ← readBytes entry.name.toUTF8.size cursor
  guard (name == entry.name.toUTF8) "central ZIP member name mismatch"
  return cursor

def decodeCandidate (bytes : ByteArray) : Except String (List Entry) := do
  guard (bytes.size ≥ 22) "truncated ZIP end record"
  let endStart := bytes.size - 22
  let cursor ← expectFields [(4, 0x06054b50), (2, 0), (2, 0)] ⟨bytes, endStart⟩
  let (count, cursor) ← readNumber 2 cursor
  let cursor ← expect 2 count cursor
  let (centralSize, cursor) ← readNumber 4 cursor
  let (centralStart, cursor) ← readNumber 4 cursor
  let cursor ← expect 2 0 cursor
  guard (cursor.position == bytes.size && centralStart + centralSize == endStart) "ZIP directory bounds mismatch"
  let (locals, cursor) ← readLocals count ⟨bytes, 0⟩
  guard (cursor.position == centralStart) "ZIP local-record bounds mismatch"
  let cursor ← locals.foldlM (fun cursor record => checkCentral record cursor) cursor
  guard (cursor.position == endStart) "ZIP central-record bounds mismatch"
  let entries := locals.map Local.entry
  guard (decide (entries.map Entry.name).Nodup) "duplicate ZIP member"
  return entries

/-- A certificate checker independent of the candidate writer and reader.
The decision is executable, and its accepting branch carries a kernel proof. -/
def check (entries : List Entry) (bytes : ByteArray) :
    Except String (PLift (Format.Conforms entries bytes)) :=
  if h : Format.Conforms entries bytes then .ok ⟨h⟩
  else .error "archive does not satisfy the stored ZIP32 byte grammar"

def decode (bytes : ByteArray) : Except String (List Entry) := do
  let entries ← decodeCandidate bytes
  let _ ← check entries bytes
  return entries

end Rumoca.EFMI.StoredZIP
