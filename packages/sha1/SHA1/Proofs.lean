import SHA1.Basic

namespace SHA1

theorem foldBlocks_zero (bytes : List UInt8) (state : State) :
    foldBlocks 0 bytes state = state := rfl

theorem foldBlocksUsing_succ (step : State → List UInt8 → State)
    (n : Nat) (bytes : List UInt8) (state : State) :
    foldBlocksUsing step (n + 1) bytes state =
      foldBlocksUsing step n (bytes.drop 64) (step state (bytes.take 64)) := rfl

theorem bigEndian_length (n count : Nat) : (bigEndian n count).length = count := by
  simp [bigEndian]

theorem pad_length (bytes : List UInt8) :
    (pad bytes).length = bytes.length + 1 + paddingCount bytes.length + 8 := by
  simp only [pad, List.length_append, List.length_cons, List.length_nil,
    List.length_replicate, bigEndian_length]

theorem pad_aligned (bytes : List UInt8) : (pad bytes).length % 64 = 0 := by
  rw [pad_length]
  unfold paddingCount
  omega

theorem pad_nonempty (bytes : List UInt8) : 64 ≤ (pad bytes).length := by
  have aligned := pad_aligned bytes
  have length := pad_length bytes
  omega

theorem digest_bytes_length (state : State) : state.bytes.length = 20 := by
  simp [State.bytes, bigEndian_length]

end SHA1
