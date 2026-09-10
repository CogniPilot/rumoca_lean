import RumocaEFMI.CRC32

/-! Byte grammar for the selected ZIP32 profile, reviewed against PKWARE's
APPNOTE §§4.3.6–4.3.16. All records are stored, unencrypted, single-disk files.
Offsets are absolute from the first byte. Names are ASCII relative paths;
extra fields, comments, descriptors, directory entries and trailing bytes are
excluded. This is a restricted format contract, not a claim about all ZIPs.

This list-based specification is separate from the cursor reader and mutable
ByteArray writer. Numeric fields use base-256 digits and explicit byte widths.
The admissibility predicate excludes silent truncation of variable fields. -/
namespace Rumoca.EFMI.StoredZIP

structure Entry where
  name : String
  bytes : ByteArray
  deriving BEq, DecidableEq

def safeName (name : String) : Bool :=
  (name.splitOn "/").all fun part => !part.isEmpty && part != "." && part != ".." &&
    part.toList.all (fun c => c.toNat < 128 && (c.isAlphanum || c == '_' || c == '-' || c == '.'))

namespace Format

/-- The least-significant base-256 digit is first. -/
def number (width value : Nat) : List UInt8 :=
  (List.range width).map fun i => (value / 256 ^ i).toUInt8

def name (entry : Entry) : List UInt8 := entry.name.toUTF8.data.toList
def payload (entry : Entry) : List UInt8 := entry.bytes.data.toList
def crc (entry : Entry) : Nat := (CRC32.checksum entry.bytes).toNat

/-- Fixed fields: signature, extraction version 1.0, flags, stored method,
midnight, DOS date 1980-01-01. Then CRC, both sizes, name size, no extra field. -/
def localRecord (entry : Entry) : List UInt8 :=
  [0x50, 0x4b, 0x03, 0x04, 10, 0, 0, 0, 0, 0, 0, 0, 33, 0] ++
  number 4 (crc entry) ++ number 4 (payload entry).length ++
  number 4 (payload entry).length ++ number 2 (name entry).length ++
  [0, 0] ++ name entry ++ payload entry

/-- Fixed central fields also specify DOS creator 2.0, no disk, attributes,
extra field or comment. The final four-byte field references the local record. -/
def centralRecord (offset : Nat) (entry : Entry) : List UInt8 :=
  [0x50, 0x4b, 0x01, 0x02, 20, 0, 10, 0, 0, 0, 0, 0, 0, 0, 33, 0] ++
  number 4 (crc entry) ++ number 4 (payload entry).length ++
  number 4 (payload entry).length ++ number 2 (name entry).length ++
  List.replicate 12 0 ++ number 4 offset ++ name entry

/-- Record offsets are accumulated from actual preceding record lengths. -/
def directory : Nat → List Entry → List UInt8
  | _, [] => []
  | offset, entry :: rest => centralRecord offset entry ++
      directory (offset + (localRecord entry).length) rest

def localRecords (entries : List Entry) : List UInt8 := entries.flatMap localRecord

/-- End of central directory: one disk, identical counts, exact size/offset,
and no archive comment. There are no permitted bytes after this record. -/
def endRecord (count size offset : Nat) : List UInt8 :=
  [0x50, 0x4b, 0x05, 0x06, 0, 0, 0, 0] ++ number 2 count ++ number 2 count ++
  number 4 size ++ number 4 offset ++ [0, 0]

def contents (entries : List Entry) : List UInt8 :=
  localRecords entries ++ directory 0 entries ++
    endRecord entries.length (directory 0 entries).length (localRecords entries).length

def entryFits (entry : Entry) : Bool :=
  safeName entry.name && entry.name.toUTF8.size < 65536 && entry.bytes.size < 2 ^ 32

/-- All names are unique; all variable-width fields fit. The local-section
bound also bounds every local offset in the central directory. -/
def Admissible (entries : List Entry) : Prop :=
  entries.length < 65536 ∧ (entries.map Entry.name).Nodup ∧
  entries.all entryFits = true ∧
  (localRecords entries).length < 2 ^ 32 ∧ (directory 0 entries).length < 2 ^ 32

instance (entries : List Entry) : Decidable (Admissible entries) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Complete-byte conformance. Neither hashes nor a producer's member list
can stand in for the bytes of the archive being certified. -/
def Conforms (entries : List Entry) (bytes : ByteArray) : Prop :=
  Admissible entries ∧ bytes.data.toList = contents entries

instance (entries : List Entry) (bytes : ByteArray) : Decidable (Conforms entries bytes) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Format
end Rumoca.EFMI.StoredZIP
