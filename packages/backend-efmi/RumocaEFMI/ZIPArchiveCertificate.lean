import RumocaEFMI.ZIPCertificate

/-! Archive assembly from separately checked text payloads and actual byte
segments. These facts do not evaluate the payload encoding or checksum again. -/
namespace Rumoca.EFMI.StoredZIP.Certificate

theorem Text.byteSize (text : Text) : text.source.toUTF8.size = text.size := by
  have h := (congrArg List.length text.encoding).trans text.length
  simpa only [Array.length_toList, ByteArray.size] using h

theorem Text.entryFits (text : Text) (name : String)
    (safe : safeName name = true) (short : name.toUTF8.size < 65536)
    (small : text.size < 2^32) :
    Format.entryFits ⟨name, text.source.toUTF8⟩ = true := by
  simp only [Format.entryFits, safe, short, text.byteSize, small, decide_true, Bool.and_self]

theorem append_length (head tail : List UInt8) (h t : Nat)
    (hh : head.length = h) (ht : tail.length = t) : (head ++ tail).length = h + t := by
  rw [List.length_append, hh, ht]

theorem append_equal (head tail expectedHead expectedTail : List UInt8)
    (hh : head = expectedHead) (ht : tail = expectedTail) :
    head ++ tail = expectedHead ++ expectedTail := by rw [hh, ht]

theorem entry_fits_cons (entry : Entry) (rest : List Entry)
    (head : Format.entryFits entry = true) (tail : rest.all Format.entryFits = true) :
    (entry :: rest).all Format.entryFits = true := by
  simp only [List.all_cons, head, tail, Bool.and_self]

end Rumoca.EFMI.StoredZIP.Certificate
