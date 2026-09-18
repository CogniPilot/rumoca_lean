import Std

/-! Raw-byte SHA-1 for the checksums required by eFMI 1.0.0 Beta 1.
The authored definition follows FIPS 180-4 §§4.1.1, 4.2.1, 5 and 6.1.2:
big-endian words, 512-bit padding, 80 scheduled words and modular 32-bit rounds.
It is an integrity field, not an authenticity or collision-resistance claim.
No native hash result is an axiom or an acceptance authority. -/
namespace SHA1

def bigEndian (n count : Nat) : List UInt8 :=
  (List.range count).map fun i => (n >>> (8 * (count - 1 - i))).toUInt8

def paddingCount (length : Nat) : Nat := (119 - length % 64) % 64

def pad (bytes : List UInt8) : List UInt8 :=
  bytes ++ [128] ++ List.replicate (paddingCount bytes.length) 0 ++ bigEndian (8 * bytes.length) 8

/-- The 32-bit word mask. Words are kept as `Nat` values below `2 ^ 32`; the
kernel evaluates the accelerated `Nat` bitwise and arithmetic operations far
more efficiently than the `Fin`-wrapped `UInt32` operations when a checksum is
certified against actual bytes. -/
def mask : Nat := 0xffffffff

def rol (x n : Nat) : Nat := ((x <<< n) ||| (x >>> (32 - n))) &&& mask

/-- One big-endian 32-bit message word from four bytes (FIPS 180-4 §5.1). -/
def messageWord (a b c d : UInt8) : Nat :=
  (a.toNat <<< 24) ||| (b.toNat <<< 16) ||| (c.toNat <<< 8) ||| d.toNat

/-- The sixteen big-endian block words, consumed four bytes at a time. A short
final group (only present for a non-aligned block) contributes no word; the
callers only pass exact 64-byte blocks. -/
def blockWords : List UInt8 → List Nat
  | a :: b :: c :: d :: rest => messageWord a b c d :: blockWords rest
  | _ => []

/-- One scheduled word W(t) from the sixteen most recent words, newest first:
positions 2, 7, 13 and 15 hold W(t-3), W(t-8), W(t-14) and W(t-16), per the
FIPS 180-4 §6.1.2 recurrence W(t) = ROTL1(W(t-3) ⊕ W(t-8) ⊕ W(t-14) ⊕ W(t-16)). -/
def scheduleWord : List Nat → Nat
  | _ :: _ :: w3 :: _ :: _ :: _ :: _ :: w8 :: _ :: _ :: _ :: _ :: _ :: w14 :: _ :: w16 :: _ =>
    rol (w3 ^^^ w8 ^^^ w14 ^^^ w16) 1
  | _ => 0

/-- Extend the newest-first word list by `count` scheduled words. -/
def extendSchedule : Nat → List Nat → List Nat
  | 0, acc => acc
  | count + 1, acc => extendSchedule count (scheduleWord acc :: acc)

/-- The eighty FIPS 180-4 schedule words in round order. The construction is a
plain structural recurrence over lists so the schedule reduces efficiently in
the kernel when a checksum is certified against actual bytes. -/
def schedule (bytes : List UInt8) : List Nat :=
  (extendSchedule 64 (blockWords bytes).reverse).reverse

structure State where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  e : Nat
  deriving Repr, BEq, DecidableEq

def initial : State := ⟨0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0⟩

def round (s : State) (t : Nat) (w : Nat) : State :=
  let f := if t < 20 then (s.b &&& s.c) ||| ((mask ^^^ s.b) &&& s.d)
    else if t < 40 then s.b ^^^ s.c ^^^ s.d
    else if t < 60 then (s.b &&& s.c) ||| (s.b &&& s.d) ||| (s.c &&& s.d)
    else s.b ^^^ s.c ^^^ s.d
  let k : Nat := if t < 20 then 0x5a827999 else if t < 40 then 0x6ed9eba1
    else if t < 60 then 0x8f1bbcdc else 0xca62c1d6
  ⟨(rol s.a 5 + f + s.e + k + w) &&& mask, s.a, rol s.b 30, s.c, s.d⟩

def compress (state : State) (block : List UInt8) : State :=
  let result := (schedule block).zipIdx.foldl (fun s p => round s p.2 p.1) state
  ⟨(state.a + result.a) &&& mask, (state.b + result.b) &&& mask, (state.c + result.c) &&& mask,
    (state.d + result.d) &&& mask, (state.e + result.e) &&& mask⟩

def foldBlocksUsing (step : State → List UInt8 → State) : Nat → List UInt8 → State → State
  | 0, _, state => state
  | n + 1, bytes, state => foldBlocksUsing step n (bytes.drop 64) (step state (bytes.take 64))

def foldBlocks (n : Nat) (bytes : List UInt8) (state : State) : State :=
  foldBlocksUsing compress n bytes state

def digest (bytes : ByteArray) : State :=
  let padded := pad bytes.data.toList
  foldBlocks (padded.length / 64) padded initial

def State.bytes (state : State) : List UInt8 :=
  [state.a, state.b, state.c, state.d, state.e].flatMap fun word => bigEndian word 4

def hex (bytes : List UInt8) : String :=
  String.ofList (bytes.flatMap fun b =>
    [b.toNat / 16, b.toNat % 16].map fun digit =>
      Char.ofNat (if digit < 10 then 48 + digit else 87 + digit))

def hash (bytes : ByteArray) : String := hex (digest bytes).bytes

/-- The bit-length field is representable without truncation. eFMU's stored
ZIP32 profile will impose the stricter 32-bit member size bound as well. -/
def ValidInput (bytes : ByteArray) : Prop := bytes.size < 2 ^ 61

end SHA1
