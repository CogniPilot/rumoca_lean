import SHA1.Certificate

namespace SHA1.Certificate

set_option maxRecDepth 10000

theorem checkBlocks_sound (step : State → List UInt8 → State) (n : Nat) (bytes : List UInt8) (current : State)
    (states : List State) (result : State)
    (h : checkBlocks step n bytes current states result = true) :
    runBlocks step n bytes current = result := by
  induction n generalizing bytes current states with
  | zero =>
    cases states with
    | nil => exact of_decide_eq_true h
    | cons next rest => simp only [checkBlocks, Bool.false_eq_true] at h
  | succ n ih =>
    cases states with
    | nil => simp [checkBlocks] at h
    | cons next rest =>
      simp only [checkBlocks, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [runBlocks, foldBlocksUsing, h.1] using ih _ next rest h.2

theorem runBlocks_compress (n : Nat) (bytes : List UInt8) (current : State) :
    runBlocks compress n bytes current = foldBlocks n bytes current := rfl

theorem hash_correct (bytes : ByteArray) (states : List State) (result : State)
    (h : check bytes states result = true) : hash bytes = hex result.bytes := by
  exact congrArg (fun state => hex state.bytes)
    ((runBlocks_compress _ _ _).symm.trans (checkBlocks_sound _ _ _ _ _ _ h))

/-- Check the UTF-8/padding conversion once, then validate block transitions
over its quoted bytes instead of repeatedly reducing the source string. -/
theorem check_of_padding (bytes : ByteArray) (padded : List UInt8) (states : List State) (result : State)
    (padding : pad bytes.data.toList = padded)
    (blocks : checkBlocks compress (padded.length / 64) padded initial states result = true) :
    check bytes states result = true := by
  unfold check
  rw [padding]
  exact blocks

/-- Reuse the standard UTF-8 encoding theorems instead of kernel-reducing
the accumulating ByteArray builder for a long string literal. -/
theorem utf8_of_chars (source : String) (chars : List Char)
    (source_eq : source = String.ofList chars) :
    source.toUTF8.data.toList = chars.flatMap String.utf8EncodeChar := by
  rw [source_eq, String.toUTF8_eq_toByteArray, String.toByteArray_ofList,
    List.utf8Encode, List.toList_data_toByteArray]

/-- Padding is a suffix determined by the checked original byte count. -/
theorem pad_of_length (bytes tail : List UInt8) (length : Nat)
    (size : bytes.length = length)
    (suffix : [128] ++ List.replicate (paddingCount length) 0 ++ bigEndian (8 * length) 8 = tail) :
    pad bytes = bytes ++ tail := by
  calc
    pad bytes = bytes ++ ([128] ++ List.replicate (paddingCount length) 0 ++ bigEndian (8 * length) 8) := by
      simp only [pad, size, List.append_assoc]
    _ = bytes ++ tail := congrArg (bytes ++ ·) suffix

/-- Lift a suffix certificate through an unchanged complete input block. -/
theorem append_suffix (block raw padded suffix : List UInt8)
    (tail : raw ++ suffix = padded) :
    (block ++ raw) ++ suffix = block ++ padded := by
  rw [List.append_assoc, tail]

/-- Compose one independently checked compression with the remaining blocks.
The fixed block width is checked separately, so no input suffix is discarded. -/
theorem block_cons (step : State → List UInt8 → State) (n : Nat)
    (block rest : List UInt8) (current next result : State)
    (width : block.length = 64) (head : step current block = next)
    (tail : foldBlocksUsing step n rest next = result) :
    foldBlocksUsing step (n + 1) (block ++ rest) current = result := by
  rw [foldBlocksUsing, ← width, List.take_left, List.drop_left, head]
  exact tail

/-- Bind a sequence of small block certificates to the exact original bytes. -/
theorem hash_of_blocks (bytes : ByteArray) (padded : List UInt8) (count : Nat) (result : State)
    (padding : pad bytes.data.toList = padded) (size : padded.length / 64 = count)
    (blocks : foldBlocksUsing compress count padded initial = result) :
    hash bytes = hex result.bytes := by
  unfold hash digest foldBlocks
  dsimp only
  rw [padding, size, blocks]

theorem buildBlocks_checked (step : State → List UInt8 → State) (n : Nat) (bytes : List UInt8) (current : State) :
    checkBlocks step n bytes current (buildBlocks step n bytes current).1
      (buildBlocks step n bytes current).2 = true := by
  induction n generalizing bytes current with
  | zero => simp only [buildBlocks, checkBlocks, decide_true]
  | succ n ih => simp only [buildBlocks, checkBlocks, decide_true, Bool.true_and, ih]

theorem build_checked (bytes : ByteArray) :
    check bytes (build bytes).1 (build bytes).2 = true := buildBlocks_checked _ _ _ _

end SHA1.Certificate
