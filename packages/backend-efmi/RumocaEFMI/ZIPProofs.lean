import RumocaEFMI.StoredZIP

namespace Rumoca.EFMI.StoredZIP

theorem littleEndian_spec (value width : Nat) :
    (littleEndian value width).data.toList = Format.number width value := by
  simp only [littleEndian, List.toList_data_toByteArray, Format.number,
    Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem fields_spec (values : List (Nat × Nat)) (initial : ByteArray) :
    (values.foldl (fun out (width, value) => out ++ littleEndian value width) initial).data.toList =
      initial.data.toList ++ values.flatMap (fun (width, value) => Format.number width value) := by
  induction values generalizing initial with
  | nil => simp
  | cons item rest ih =>
    simp only [List.foldl_cons, ih, ByteArray.toList_data_append, littleEndian_spec,
      List.flatMap_cons, List.append_assoc]

theorem localHeader_spec (entry : Entry) :
    (localHeader entry (CRC32.checksum entry.bytes) ++ entry.bytes).data.toList =
      Format.localRecord entry := by
  simp only [localHeader, fields, ByteArray.toList_data_append, fields_spec,
    ByteArray.data_empty, Array.toList_empty, List.nil_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Format.localRecord, Format.crc, Format.payload, Format.name,
    Array.length_toList, ByteArray.size_data]
  simp only [Format.number, List.range_succ, List.range_zero,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  rfl

theorem centralHeader_spec (entry : Entry) (offset : Nat) :
    (centralHeader entry (CRC32.checksum entry.bytes) offset).data.toList =
      Format.centralRecord offset entry := by
  simp only [centralHeader, fields, ByteArray.toList_data_append, fields_spec,
    ByteArray.data_empty, Array.toList_empty, List.nil_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Format.centralRecord, Format.crc, Format.payload, Format.name,
    Array.length_toList, ByteArray.size_data]
  simp only [Format.number, List.range_succ, List.range_zero,
    List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append]
  rfl

theorem endRecord_spec (count size offset : Nat) :
    (endRecord count size offset).data.toList = Format.endRecord count size offset := by
  simp only [endRecord, fields, fields_spec, ByteArray.data_empty, Array.toList_empty,
    List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, Format.endRecord]
  simp only [Format.number, List.range_succ, List.range_zero,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  rfl

private theorem guard_bind_ok {condition : Bool} {message : String}
    {next : Unit → Except String α} {result : α}
    (h : (guard condition message >>= next) = .ok result) :
    condition = true ∧ next () = .ok result := by
  cases condition <;> simp_all [guard, bind, Except.bind]

/-- The tail-recursive ByteArray builder refines the list byte grammar. Its
invariant includes valid members and representable section sizes. -/
theorem writeRecords_spec {entries : List Entry} {first second out₁ out₂ : ByteArray}
    (start₁ : first.size < 2 ^ 32) (start₂ : second.size < 2 ^ 32)
    (h : writeRecords entries first second = .ok (out₁, out₂)) :
    entries.all Format.entryFits = true ∧ out₁.size < 2 ^ 32 ∧ out₂.size < 2 ^ 32 ∧
    out₁.data.toList = first.data.toList ++ Format.localRecords entries ∧
    out₂.data.toList = second.data.toList ++ Format.directory first.size entries := by
  induction entries generalizing first second with
  | nil =>
    cases h
    simp [start₁, start₂, Format.localRecords, Format.directory]
  | cons entry rest ih =>
    simp only [writeRecords] at h
    obtain ⟨fits, h⟩ := guard_bind_ok h
    obtain ⟨sizes, h⟩ := guard_bind_ok h
    have bounds :
        (first ++ (localHeader entry (CRC32.checksum entry.bytes) ++ entry.bytes)).size < 2 ^ 32 ∧
        (second ++ centralHeader entry (CRC32.checksum entry.bytes) first.size).size < 2 ^ 32 := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using sizes
    obtain ⟨allFit, bound₁, bound₂, localEq, centralEq⟩ := ih bounds.1 bounds.2 h
    refine ⟨by simp [fits, allFit], bound₁, bound₂, ?_, ?_⟩
    · rw [ByteArray.toList_data_append, localHeader_spec] at localEq
      simpa only [Format.localRecords, List.flatMap_cons, List.append_assoc] using localEq
    · have sizeEq :
          (localHeader entry (CRC32.checksum entry.bytes) ++ entry.bytes).size =
            (Format.localRecord entry).length := by
        rw [← localHeader_spec, Array.length_toList, ByteArray.size_data]
      simpa only [ByteArray.toList_data_append, centralHeader_spec,
        ByteArray.size_append, sizeEq, Format.directory, List.append_assoc] using centralEq

/-- Successful generation itself meets the format contract; the independent
checker is not being used to mask a missing writer refinement theorem. -/
theorem encode_sound {entries : List Entry} {bytes : ByteArray}
    (h : encode entries = .ok bytes) : Format.Conforms entries bytes := by
  simp only [encode] at h
  obtain ⟨count, h⟩ := guard_bind_ok h
  obtain ⟨unique, h⟩ := guard_bind_ok h
  cases records : writeRecords entries ByteArray.empty ByteArray.empty with
  | error error => simp only [records, bind, Except.bind] at h; contradiction
  | ok pair =>
    obtain ⟨first, second⟩ := pair
    simp only [records, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst bytes
    obtain ⟨fits, bound₁, bound₂, localEq, centralEq⟩ :=
      writeRecords_spec (by decide) (by decide) records
    simp only [ByteArray.data_empty, Array.toList_empty, List.nil_append,
      ByteArray.size_empty] at localEq centralEq
    have size₁ : first.size = (Format.localRecords entries).length := by
      rw [← localEq, Array.length_toList, ByteArray.size_data]
    have size₂ : second.size = (Format.directory 0 entries).length := by
      rw [← centralEq, Array.length_toList, ByteArray.size_data]
    refine ⟨⟨by simpa using count, by simpa using unique, fits,
      size₁ ▸ bound₁, size₂ ▸ bound₂⟩, ?_⟩
    simp only [ByteArray.toList_data_append, endRecord_spec, localEq, centralEq,
      size₁, size₂, Format.contents]

theorem writeRecords_complete {entries : List Entry} {first second : ByteArray}
    (fits : entries.all Format.entryFits = true)
    (bound₁ : first.size + (Format.localRecords entries).length < 2 ^ 32)
    (bound₂ : second.size + (Format.directory first.size entries).length < 2 ^ 32) :
    ∃ result, writeRecords entries first second = .ok result := by
  induction entries generalizing first second with
  | nil => exact ⟨(first, second), rfl⟩
  | cons entry rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at fits
    let next₁ := first ++ (localHeader entry (CRC32.checksum entry.bytes) ++ entry.bytes)
    let next₂ := second ++ centralHeader entry (CRC32.checksum entry.bytes) first.size
    have size₁ : next₁.size = first.size + (Format.localRecord entry).length := by
      simp only [next₁, ByteArray.size_append]
      have := congrArg List.length (localHeader_spec entry)
      simpa only [Array.length_toList, ByteArray.size_data, ByteArray.size_append] using
        congrArg (first.size + ·) this
    have size₂ : next₂.size = second.size + (Format.centralRecord first.size entry).length := by
      simp only [next₂, ByteArray.size_append]
      have := congrArg List.length (centralHeader_spec entry first.size)
      simpa only [Array.length_toList, ByteArray.size_data] using
        congrArg (second.size + ·) this
    have tail₁ : next₁.size + (Format.localRecords rest).length < 2 ^ 32 := by
      simpa only [size₁, Format.localRecords, List.flatMap_cons, List.length_append,
        Nat.add_assoc] using bound₁
    have tail₂ : next₂.size + (Format.directory next₁.size rest).length < 2 ^ 32 := by
      simpa only [size₁, size₂, Format.directory, List.length_append, Nat.add_assoc] using bound₂
    have nextBound₁ : next₁.size < 2 ^ 32 := by omega
    have nextBound₂ : next₂.size < 2 ^ 32 := by omega
    obtain ⟨result, successful⟩ := ih fits.2 tail₁ tail₂
    refine ⟨result, ?_⟩
    simp only [writeRecords, guard, fits.1, if_true, bind, Except.bind]
    change (if decide (next₁.size < 2 ^ 32) && decide (next₂.size < 2 ^ 32) then
      .ok () else .error "ZIP32 archive size exceeded") >>= (fun _ => writeRecords rest next₁ next₂) =
        .ok result
    simpa only [nextBound₁, nextBound₂, decide_true, Bool.and_true, if_true,
      bind, Except.bind] using successful

/-- Every admissible member sequence is serializable. Together with soundness
this rules out a vacuous generator that simply rejects all inputs. -/
theorem encode_complete {entries : List Entry} (h : Format.Admissible entries) :
    ∃ bytes, encode entries = .ok bytes ∧ Format.Conforms entries bytes := by
  obtain ⟨count, unique, fits, bound₁, bound₂⟩ := h
  obtain ⟨⟨first, second⟩, records⟩ := writeRecords_complete
    (first := ByteArray.empty) (second := ByteArray.empty) fits
    (by simpa using bound₁) (by simpa using bound₂)
  have successful : encode entries =
      .ok (first ++ second ++ endRecord entries.length second.size first.size) := by
    simp only [encode, guard, count, unique, decide_true, if_true,
      bind, Except.bind, records, pure, Except.pure]
  exact ⟨_, successful, encode_sound successful⟩

theorem check_accepts_iff (entries : List Entry) (bytes : ByteArray) :
    (check entries bytes).isOk = true ↔ Format.Conforms entries bytes := by
  unfold check
  split <;> simp_all [Except.isOk, Except.toBool]

/-- Universal parsing contract, including adversarial bytes and arbitrary
candidate-reader results. This is soundness for the selected stored profile;
it does not assert acceptance of other legal ZIP encodings. -/
theorem decode_sound {entries : List Entry} {bytes : ByteArray}
    (h : decode bytes = .ok entries) : Format.Conforms entries bytes := by
  unfold decode at h
  cases candidate : decodeCandidate bytes <;> simp only [candidate, bind, Except.bind] at h
  · contradiction
  rename_i result
  cases checked : check result bytes <;> simp only [checked, pure, Except.pure] at h
  · contradiction
  rename_i proof
  cases h
  exact proof.down

namespace Format

theorem number_length (width value : Nat) : (number width value).length = width := by
  simp [number]

/-- No truncation of any representable numeric field, for every width and
value. The cursor reader uses precisely this base-256 fold. -/
theorem number_value {width value : Nat} (fits : value < 256 ^ width) :
    (number width value).foldr (fun byte rest => byte.toNat + 256 * rest) 0 = value := by
  induction width generalizing value with
  | zero =>
    simp only [Nat.pow_zero] at fits
    have : value = 0 := by omega
    simp [number, this]
  | succ width ih =>
    have tailEq :
        (List.range width).map (fun i => (value / 256 ^ (i + 1)).toUInt8) =
          number width (value / 256) := by
      simp only [number, Nat.pow_succ', Nat.div_div_eq_div_mul]
    have tailFits : value / 256 < 256 ^ width := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 256)).mpr
      simpa only [Nat.pow_succ] using fits
    rw [number, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [Nat.pow_zero, Nat.div_one, List.foldr_cons, Function.comp_def, Nat.succ_eq_add_one]
    rw [tailEq, ih tailFits]
    exact Nat.mod_add_div value 256

theorem localRecord_length (entry : Entry) :
    (localRecord entry).length = 30 + (name entry).length + (payload entry).length := by
  simp [localRecord, number_length]
  omega

theorem centralRecord_length (offset : Nat) (entry : Entry) :
    (centralRecord offset entry).length = 46 + (name entry).length := by
  simp [centralRecord, number_length]
  omega

theorem endRecord_length (count size offset : Nat) :
    (endRecord count size offset).length = 22 := by
  simp [endRecord, number_length]

theorem conforms_names_unique {entries : List Entry} {bytes : ByteArray}
    (h : Conforms entries bytes) : (entries.map Entry.name).Nodup := h.1.2.1

theorem conforms_entries_fit {entries : List Entry} {bytes : ByteArray}
    (h : Conforms entries bytes) {entry : Entry} (mem : entry ∈ entries) :
    safeName entry.name = true ∧ entry.name.toUTF8.size < 65536 ∧ entry.bytes.size < 2 ^ 32 := by
  have fit := List.all_eq_true.mp h.1.2.2.1 entry mem
  simpa [entryFits, Bool.and_eq_true, and_assoc] using fit

/-- The exact member bytes occur in a local record of the actual archive.
The record contains the CRC of these same bytes, not a hash supplied by a
producer. Complete conformance also fixes every central reference and EOCD. -/
theorem conforms_member {entries : List Entry} {bytes : ByteArray}
    (h : Conforms entries bytes) {entry : Entry} (mem : entry ∈ entries) :
    ∃ before after : List UInt8,
      bytes.data.toList = before ++ localRecord entry ++ after := by
  obtain ⟨pre, post, rfl⟩ := List.mem_iff_append.mp mem
  refine ⟨localRecords pre, localRecords post ++ directory 0 (pre ++ entry :: post) ++
    endRecord (pre ++ entry :: post).length
      (directory 0 (pre ++ entry :: post)).length
      (localRecords (pre ++ entry :: post)).length, ?_⟩
  rw [h.2]
  simp only [contents, localRecords, List.flatMap_append, List.flatMap_cons, List.append_assoc]

/-- Complete bytes are determined by the member sequence, including record
metadata. A certificate about another archive cannot authorize this one. -/
theorem conforms_bytes_unique {entries : List Entry} {a b : ByteArray}
    (ha : Conforms entries a) (hb : Conforms entries b) : a = b := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  exact ha.2.trans hb.2.symm

end Format
end Rumoca.EFMI.StoredZIP
