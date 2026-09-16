import Rumoca.EFMIArchive
import SHA1
import Std.Time.Format

/-! Emitted eFMI manifest identities. Two modes share one brace-delimited
8-4-4-4-12 layout formatter, so the actual-file certificate's `Identity.Valid`
and `Identity.Distinct` checks apply to both without change.

Default mode draws entropy from the operating system and stamps RFC 9562 §4.4
version 4 identifiers with a wall-clock generation time. When the standard
`SOURCE_DATE_EPOCH` environment variable is set, the generation time is that
fixed UTC instant and the three identifiers are RFC 9562 §5.5 version 5
name-based (SHA-1) values over a fixed Rumoca namespace and the role, model
name, complete source text and epoch. Identical inputs then produce identical
identities, which is the caller's responsibility under `SOURCE_DATE_EPOCH`; the
Lean checker still verifies only layout, UTC validity and distinctness within
one archive, never global uniqueness or the accuracy of a supplied clock. -/
namespace Rumoca.EFMIIdentity
open Std.Time

/-- Fixed Rumoca eFMI identity namespace UUID for RFC 9562 §5.5 name-based
derivation: `{a1e6b3c9-5d24-4f8b-9c07-3e1f2a4b6d80}`, its sixteen octets in
network byte order. -/
def namespaceBytes : ByteArray :=
  ⟨#[0xa1, 0xe6, 0xb3, 0xc9, 0x5d, 0x24, 0x4f, 0x8b,
     0x9c, 0x07, 0x3e, 0x1f, 0x2a, 0x4b, 0x6d, 0x80]⟩

/-- Stamp the RFC 9562 §4.1 version nibble (high nibble of octet 6) and the
`10` variant bits (high bits of octet 8) into a sixteen-octet identifier. -/
def stamp (versionNibble : UInt8) (bytes : ByteArray) : ByteArray :=
  let bytes := bytes.set! 6 ((bytes[6]! &&& 0x0f) ||| versionNibble)
  bytes.set! 8 ((bytes[8]! &&& 0x3f) ||| 0x80)

/-- Render sixteen octets in the eFMI brace-delimited 8-4-4-4-12 hexadecimal
UUID layout. `SHA1.hex` is used here only as a lowercase byte-to-hex encoder. -/
def format (bytes : ByteArray) : String :=
  let digits := (SHA1.hex bytes.data.toList).toList
  let fields := [(0, 8), (8, 4), (12, 4), (16, 4), (20, 12)]
  "{" ++ String.intercalate "-" (fields.map fun (offset, width) =>
    String.ofList ((digits.drop offset).take width)) ++ "}"

/-- Candidate version 4 UUID. The operating system supplies entropy; the
actual-file certificate checks identity validity and distinctness within this
archive, not global uniqueness. -/
def randomUUID : IO String := do
  let raw ← IO.getRandomBytes 16
  if raw.size != 16 then throw (IO.userError "Could not obtain eFMI identity bytes")
  return format (stamp 0x40 raw)

/-- Version 5 name-based UUID: SHA-1 over the Rumoca namespace and `name`, with
the leading sixteen octets stamped and formatted. Identical names yield
identical identifiers. -/
def derivedUUID (name : String) : String :=
  let digest := (SHA1.digest (namespaceBytes ++ name.toUTF8)).bytes
  format (stamp 0x50 ⟨(digest.take 16).toArray⟩)

/-- Format an instant as the eFMI `generationDateAndTime` UTC-second string. -/
def formatInstant (timestamp : Timestamp) : String :=
  timestamp.toPlainDateTimeAssumingUTC.format "uuuu-MM-dd'T'HH:mm:ss'Z'"

/-- The UTC-second `generationDateAndTime` string for whole seconds since the
Unix epoch, as carried by `SOURCE_DATE_EPOCH`. -/
def epochGenerated (epoch : Nat) : String :=
  formatInstant (Timestamp.ofSecondsSinceUnixEpoch
    (Std.Time.Internal.UnitVal.ofNat epoch : Second.Offset))

/-- The name-based derivation input for one manifest role, binding the role, the
originating model name, the complete source text and the epoch string. -/
def derivedName (role model source : String) (epoch : Nat) : String :=
  s!"{role}\n{model}\n{source}\n{epoch}"

/-- Deterministic version 5 identity for a fixed `SOURCE_DATE_EPOCH`. The three
role identifiers differ, so `Identity.Distinct` holds; the checker verifies this
independently at check time. -/
def derivedIdentity (model source : String) (epoch : Nat) : EFMI.Manifest.Identity :=
  ⟨derivedUUID (derivedName "container" model source epoch),
   derivedUUID (derivedName "algorithm" model source epoch),
   derivedUUID (derivedName "production" model source epoch),
   epochGenerated epoch⟩

/-- Choose the identity mode from `SOURCE_DATE_EPOCH`: reproducible version 5
identifiers and a fixed instant when it is set and parses, or version 4
identifiers and the wall clock when it is unset. A set but unparsable value is a
hard error rather than a silent fallback. -/
def identity (model source : String) : IO EFMI.Manifest.Identity := do
  match ← IO.getEnv "SOURCE_DATE_EPOCH" with
  | none =>
    let container ← randomUUID
    let algorithm ← randomUUID
    let production ← randomUUID
    let generated := formatInstant (← Timestamp.now)
    return ⟨container, algorithm, production, generated⟩
  | some raw =>
    match raw.trim.toNat? with
    | none => throw (IO.userError
        s!"SOURCE_DATE_EPOCH must be whole seconds since the Unix epoch, got: {raw}")
    | some epoch => return derivedIdentity model source epoch

end Rumoca.EFMIIdentity
