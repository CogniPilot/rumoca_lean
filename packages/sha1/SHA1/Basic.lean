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

def rol (x n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))

def word (bytes : Array UInt8) (index : Nat) : UInt32 :=
  (List.range 4).foldl (fun acc i => (acc <<< 8) + (bytes[index * 4 + i]?.getD 0).toUInt32) 0

def schedule (bytes : List UInt8) : Array UInt32 := Id.run do
  let block := bytes.toArray
  let mut words := (List.range 16).toArray.map (word block)
  for t in [16:80] do
    let w := words[t - 3]?.getD 0 ^^^ words[t - 8]?.getD 0 ^^^
      words[t - 14]?.getD 0 ^^^ words[t - 16]?.getD 0
    words := words.push (rol w 1)
  return words

structure State where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32
  deriving Repr, BEq, DecidableEq

def initial : State := ⟨0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0⟩

def round (s : State) (t : Nat) (w : UInt32) : State :=
  let f := if t < 20 then (s.b &&& s.c) ||| (~~~s.b &&& s.d)
    else if t < 40 then s.b ^^^ s.c ^^^ s.d
    else if t < 60 then (s.b &&& s.c) ||| (s.b &&& s.d) ||| (s.c &&& s.d)
    else s.b ^^^ s.c ^^^ s.d
  let k : UInt32 := if t < 20 then 0x5a827999 else if t < 40 then 0x6ed9eba1
    else if t < 60 then 0x8f1bbcdc else 0xca62c1d6
  ⟨rol s.a 5 + f + s.e + k + w, s.a, rol s.b 30, s.c, s.d⟩

def compress (state : State) (block : List UInt8) : State :=
  let words := schedule block
  let result := (List.range 80).foldl (fun s t => round s t (words[t]?.getD 0)) state
  ⟨state.a + result.a, state.b + result.b, state.c + result.c,
    state.d + result.d, state.e + result.e⟩

def foldBlocksUsing (step : State → List UInt8 → State) : Nat → List UInt8 → State → State
  | 0, _, state => state
  | n + 1, bytes, state => foldBlocksUsing step n (bytes.drop 64) (step state (bytes.take 64))

def foldBlocks (n : Nat) (bytes : List UInt8) (state : State) : State :=
  foldBlocksUsing compress n bytes state

def digest (bytes : ByteArray) : State :=
  let padded := pad bytes.data.toList
  foldBlocks (padded.length / 64) padded initial

def State.bytes (state : State) : List UInt8 :=
  [state.a, state.b, state.c, state.d, state.e].flatMap fun word => bigEndian word.toNat 4

def hex (bytes : List UInt8) : String :=
  String.ofList (bytes.flatMap fun b =>
    [b.toNat / 16, b.toNat % 16].map fun digit =>
      Char.ofNat (if digit < 10 then 48 + digit else 87 + digit))

def hash (bytes : ByteArray) : String := hex (digest bytes).bytes

/-- The bit-length field is representable without truncation. eFMU's stored
ZIP32 profile will impose the stricter 32-bit member size bound as well. -/
def ValidInput (bytes : ByteArray) : Prop := bytes.size < 2 ^ 61

end SHA1
