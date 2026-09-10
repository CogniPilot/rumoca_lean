import RumocaEFMI.ZIPProofs

/-! Compositional facts for actual ZIP certificates. Bounded checksum and
encoding facts are checked separately, then composed through these theorems;
the complete byte grammar and CRC recurrence remain unchanged. -/
namespace Rumoca.EFMI.StoredZIP.Certificate

/-- Cached facts about an exact text payload. A different string must supply
its own encoding, length and checksum proofs. -/
structure Text where
  source : String
  bytes : List UInt8
  size : Nat
  crc : UInt32
  encoding : source.toUTF8.data.toList = bytes
  length : bytes.length = size
  checksum : CRC32.checksum source.toUTF8 = crc

theorem utf8_of_chars (source : String) (chars : List Char)
    (h : source = String.ofList chars) :
    source.toUTF8.data.toList = chars.flatMap String.utf8EncodeChar := by
  rw [h, String.toUTF8_eq_toByteArray, String.toByteArray_ofList,
    List.utf8Encode, List.toList_data_toByteArray]

theorem encode_cons (chars rest : List Char) (bytes tail : List UInt8)
    (head : chars.flatMap String.utf8EncodeChar = bytes)
    (suffix : rest.flatMap String.utf8EncodeChar = tail) :
    (chars ++ rest).flatMap String.utf8EncodeChar = bytes ++ tail := by
  rw [List.flatMap_append, head, suffix]

theorem crc_cons (bytes rest : List UInt8) (before after result : UInt32)
    (head : bytes.foldl CRC32.byte before = after)
    (tail : rest.foldl CRC32.byte after = result) :
    (bytes ++ rest).foldl CRC32.byte before = result := by
  rw [List.foldl_append, head, tail]

theorem crc_of_bytes (bytes : ByteArray) (raw : List UInt8) (state : UInt32)
    (h : bytes.data.toList = raw) (run : raw.foldl CRC32.byte 0xffffffff = state) :
    CRC32.checksum bytes = state ^^^ 0xffffffff := by
  unfold CRC32.checksum
  rw [← Array.foldl_toList, h, run]

def localPrefix (crc size : Nat) (name : List UInt8) : List UInt8 :=
  [0x50, 0x4b, 0x03, 0x04, 10, 0, 0, 0, 0, 0, 0, 0, 33, 0] ++
  Format.number 4 crc ++ Format.number 4 size ++ Format.number 4 size ++
  Format.number 2 name.length ++ [0, 0] ++ name

def centralBytes (offset crc size : Nat) (name : List UInt8) : List UInt8 :=
  [0x50, 0x4b, 0x01, 0x02, 20, 0, 10, 0, 0, 0, 0, 0, 0, 0, 33, 0] ++
  Format.number 4 crc ++ Format.number 4 size ++ Format.number 4 size ++
  Format.number 2 name.length ++ List.replicate 12 0 ++ Format.number 4 offset ++ name

theorem localRecord_parts (entry : Entry) (name payload : List UInt8) (crc : UInt32) (size : Nat)
    (hn : Format.name entry = name) (hp : Format.payload entry = payload)
    (hc : CRC32.checksum entry.bytes = crc) (hs : payload.length = size) :
    Format.localRecord entry = localPrefix crc.toNat size name ++ payload := by
  simp only [Format.localRecord, Format.crc, hn, hp, hc, hs, localPrefix, List.append_assoc]

theorem centralRecord_parts (entry : Entry) (name payload : List UInt8) (crc : UInt32)
    (offset size : Nat) (hn : Format.name entry = name) (hp : Format.payload entry = payload)
    (hc : CRC32.checksum entry.bytes = crc) (hs : payload.length = size) :
    Format.centralRecord offset entry = centralBytes offset crc.toNat size name := by
  simp only [Format.centralRecord, Format.crc, hn, hp, hc, hs, centralBytes]

theorem local_cons (entry : Entry) (rest : List Entry) (head tail : List UInt8)
    (hh : Format.localRecord entry = head) (ht : Format.localRecords rest = tail) :
    Format.localRecords (entry :: rest) = head ++ tail := by
  simp only [Format.localRecords, List.flatMap_cons] at *
  rw [hh, ht]

theorem directory_cons (entry : Entry) (rest : List Entry) (offset next : Nat)
    (head tail : List UInt8) (hh : Format.centralRecord offset entry = head)
    (hs : offset + (Format.localRecord entry).length = next)
    (ht : Format.directory next rest = tail) :
    Format.directory offset (entry :: rest) = head ++ tail := by
  rw [Format.directory, hh, hs, ht]

/-- Complete-byte composition. In particular, the final component must be
exactly the end record; this leaves no room for unchecked trailing bytes. -/
theorem archive (entries : List Entry) (bytes : ByteArray) (locals central ending : List UInt8)
    (localSize centralSize : Nat)
    (count : entries.length < 65536) (unique : (entries.map Entry.name).Nodup)
    (fits : entries.all Format.entryFits = true)
    (hl : Format.localRecords entries = locals) (hc : Format.directory 0 entries = central)
    (sl : locals.length = localSize) (sc : central.length = centralSize)
    (bl : localSize < 2^32) (bc : centralSize < 2^32)
    (he : Format.endRecord entries.length centralSize localSize = ending)
    (actual : bytes.data.toList = locals ++ central ++ ending) : Format.Conforms entries bytes := by
  refine ⟨⟨count, unique, fits, ?_, ?_⟩, ?_⟩
  · simpa only [hl, sl] using bl
  · simpa only [hc, sc] using bc
  · rw [Format.contents, hl, hc, sl, sc, he]
    exact actual

end Rumoca.EFMI.StoredZIP.Certificate
