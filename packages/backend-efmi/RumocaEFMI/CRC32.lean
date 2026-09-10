import Std

/-! The reflected IEEE CRC-32 used by ZIP's stored-member profile.
It checks transport integrity; the semantic certificate still binds every
member's complete bytes independently of this checksum. -/
namespace Rumoca.EFMI.CRC32

def bit (crc : UInt32) : UInt32 :=
  if crc &&& 1 = 0 then crc >>> 1 else (crc >>> 1) ^^^ 0xedb88320

def bits : Nat → UInt32 → UInt32
  | 0, crc => crc
  | n + 1, crc => bits n (bit crc)

def byte (crc : UInt32) (value : UInt8) : UInt32 := bits 8 (crc ^^^ value.toUInt32)

def checksum (bytes : ByteArray) : UInt32 :=
  bytes.data.foldl byte 0xffffffff ^^^ 0xffffffff

end Rumoca.EFMI.CRC32
