import SHA1.Basic

/-! A checked compression trace avoids expanding a long nested hash expression
inside the kernel. Candidate states are ordinary untrusted data. Every block
transition, the exact message padding and the final state must be checked. -/
namespace SHA1.Certificate

abbrev runBlocks := foldBlocksUsing

def checkBlocks (step : State → List UInt8 → State) : Nat → List UInt8 → State → List State → State → Bool
  | 0, _, current, [], result => decide (current = result)
  | n + 1, bytes, current, next :: rest, result =>
    decide (step current (bytes.take 64) = next) &&
      checkBlocks step n (bytes.drop 64) next rest result
  | _, _, _, _, _ => false

def check (bytes : ByteArray) (states : List State) (result : State) : Bool :=
  let padded := pad bytes.data.toList
  checkBlocks compress (padded.length / 64) padded initial states result

def buildBlocks (step : State → List UInt8 → State) : Nat → List UInt8 → State → List State × State
  | 0, _, current => ([], current)
  | n + 1, bytes, current =>
    let next := step current (bytes.take 64)
    let tail := buildBlocks step n (bytes.drop 64) next
    (next :: tail.1, tail.2)

def build (bytes : ByteArray) : List State × State :=
  let padded := pad bytes.data.toList
  buildBlocks compress (padded.length / 64) padded initial

end SHA1.Certificate
