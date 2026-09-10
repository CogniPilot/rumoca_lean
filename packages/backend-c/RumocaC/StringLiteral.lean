import RumocaC.Tree
import Mathlib.Logic.Relation

/-! Literal printing under the eight-bit ASCII C profile. The independent
syntax follows C11 N1570 6.4.4.4 and 6.4.5; character rewrites follow 5.1.1.2
and 5.2.1.1. Ordinary source/execution character encodings are ASCII here.
The deterministic decoder is a proof device, not an executable compiler pass.

The contract includes all UTF-8 bytes and the appended zero. Embedded zeros
are preserved; null-free strings, static storage, pointer decay, headers and
surrounding C syntax require their separate contracts. -/
namespace Rumoca.CString

/-- Selected C11 character and escape productions; octal escapes have exactly
three digits, so a following digit cannot change their interpretation. -/
def octal (c : Char) : Option Nat :=
  if 48 ≤ c.toNat ∧ c.toNat < 56 then some (c.toNat - 48) else none

def decodeAtom : List Char → Option UInt8
  | ['\\', '"'] => some 34
  | ['\\', '\\'] => some 92
  | ['\\', '?'] => some 63
  | ['\\', a, b, c] => do
      let n := 64 * (← octal a) + 8 * (← octal b) + (← octal c)
      if n < 256 then some (UInt8.ofNat n) else none
  | [c] =>
      if 32 ≤ c.toNat ∧ c.toNat ≤ 126 ∧ c ≠ '"' ∧ c ≠ '\\'
      then some (UInt8.ofNat c.toNat) else none
  | _ => none

inductive Fragments : List Char → List UInt8 → Prop
  | nil : Fragments [] []
  | cons : decodeAtom text = some byte → Fragments rest bytes →
      Fragments (text ++ rest) (byte :: bytes)

/-- Literal storage includes C's appended zero byte, including for an empty
literal. Embedded zero bytes in the payload remain present. -/
def Denotes (text : List Char) (object : List UInt8) : Prop :=
  ∃ body bytes, text = '"' :: body ++ ['"'] ∧ Fragments body bytes ∧ object = bytes ++ [0]

/-- A stronger sufficient condition than trigraph-freedom: no adjacent question
marks, even when the preceding character came from another fragment. -/
def safeFrom : Bool → List Char → Bool
  | _, [] => true
  | previous, c :: cs => !(previous && c == '?') && safeFrom (c == '?') cs

def endMark (text : List Char) (previous : Bool) : Bool :=
  text.foldl (fun _ c => c == '?') previous

theorem safe_append (left right : List Char) (previous : Bool) :
    safeFrom previous (left ++ right) =
      (safeFrom previous left && safeFrom (endMark left previous) right) := by
  induction left generalizing previous with
  | nil => simp [safeFrom, endMark]
  | cons c cs ih => simp [safeFrom, endMark, ih, Bool.and_assoc]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem byte_correct : ∀ b : UInt8, decodeAtom (CTree.quoteByte b).toList = some b := by
  have finite : ∀ n : Fin 256, decodeAtom (CTree.quoteByte (UInt8.ofNat n.val)).toList =
      some (UInt8.ofNat n.val) := by decide +kernel
  intro b
  simpa using finite ⟨b.toNat, b.toNat_lt_size⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem byte_safe : ∀ (b : UInt8) (previous : Bool), safeFrom previous (CTree.quoteByte b).toList = true := by
  have finite : ∀ (n : Fin 256) (previous : Bool),
      safeFrom previous (CTree.quoteByte (UInt8.ofNat n.val)).toList = true := by decide +kernel
  intro b previous
  simpa using finite ⟨b.toNat, b.toNat_lt_size⟩ previous

theorem join_toList (strings : List String) :
    (String.join strings).toList = strings.flatMap String.toList := by
  have go : ∀ strings : List String, ∀ start : String,
      (strings.foldl (· ++ ·) start).toList = start.toList ++ strings.flatMap String.toList := by
    intro strings
    induction strings with
    | nil => intro start; simp
    | cons s ss ih => intro start; simp [List.foldl, ih, String.toList_append, List.append_assoc]
  simpa [String.join] using go strings ""

theorem fragments_encoded (bytes : List UInt8) :
    Fragments ((bytes.map CTree.quoteByte).flatMap String.toList) bytes := by
  induction bytes with
  | nil => exact .nil
  | cons b bs ih => exact .cons (byte_correct b) ih

theorem encoded_safe (bytes : List UInt8) (previous : Bool) :
    safeFrom previous ((bytes.map CTree.quoteByte).flatMap String.toList) = true := by
  induction bytes generalizing previous with
  | nil => rfl
  | cons b bs ih => simp [safe_append, byte_safe, ih]

theorem quote_correct (s : String) : Denotes (CTree.quote s).toList (s.toUTF8.data.toList ++ [0]) := by
  refine ⟨_, _, ?_, fragments_encoded s.toUTF8.data.toList, rfl⟩
  simp [CTree.quote, String.toList_append, join_toList]

theorem quote_safe (s : String) : safeFrom false (CTree.quote s).toList = true := by
  simp [CTree.quote, String.toList_append, join_toList, safeFrom, safe_append, encoded_safe]


/-- Deterministic decoding of the next C literal byte in this subset. -/
def decodePrefix : List Char → Option (UInt8 × List Char)
  | '\\' :: '"' :: rest => some (34, rest)
  | '\\' :: '\\' :: rest => some (92, rest)
  | '\\' :: '?' :: rest => some (63, rest)
  | '\\' :: a :: b :: c :: rest => do
      let n := 64 * (← octal a) + 8 * (← octal b) + (← octal c)
      if n < 256 then some (UInt8.ofNat n, rest) else none
  | c :: rest =>
      if 32 ≤ c.toNat ∧ c.toNat ≤ 126 ∧ c ≠ '"' ∧ c ≠ '\\'
      then some (UInt8.ofNat c.toNat, rest) else none
  | [] => none

theorem decodePrefix_atom (text rest : List Char) (byte : UInt8)
    (h : decodeAtom text = some byte) :
    decodePrefix (text ++ rest) = some (byte, rest) := by
  unfold decodeAtom at h
  split at h
  all_goals simp_all [decodePrefix]
  rename_i a b c
  by_cases ha : a = '"'
  · subst a; simp [octal] at h
  by_cases hb : a = '\\'
  · subst a; simp [octal] at h
  by_cases hc : a = '?'
  · subst a; simp [octal] at h
  cases oa : octal a <;> simp_all
  cases ob : octal b <;> simp_all
  cases oc : octal c <;> simp_all

def decodeBytes : Nat → List Char → Option (List UInt8)
  | 0, _ => none
  | fuel + 1, text =>
      if text = [] then some [] else do
        let (byte, rest) ← decodePrefix text
        let bytes ← decodeBytes fuel rest
        some (byte :: bytes)

theorem Fragments.decode (h : Fragments text bytes) (fuel : Nat)
    (enough : bytes.length < fuel) : decodeBytes fuel text = some bytes := by
  induction h generalizing fuel with
  | nil =>
    cases fuel with
    | zero => simp at enough
    | succ n => rfl
  | @cons atom byte rest bytes atom_ok tail ih =>
    have hp := decodePrefix_atom atom rest byte atom_ok
    have nonempty : atom ++ rest ≠ [] := by
      intro empty
      simp [empty, decodePrefix] at hp
    cases fuel with
    | zero => simp at enough
    | succ n =>
      have htail : bytes.length < n := by simp at enough; omega
      simp [decodeBytes, nonempty, hp, ih n htail]

theorem Fragments.unique (first : Fragments text a) (second : Fragments text b) : a = b := by
  have ha := first.decode (a.length + b.length + 1) (by omega)
  have hb := second.decode (a.length + b.length + 1) (by omega)
  exact Option.some.inj (ha.symm.trans hb)

theorem denotes_unique (first : Denotes text a) (second : Denotes text b) : a = b := by
  obtain ⟨bodyA, bytesA, ha, fa, oa⟩ := first
  obtain ⟨bodyB, bytesB, hb, fb, ob⟩ := second
  have bodies : bodyA = bodyB := List.append_cancel_right (List.cons.inj (ha.symm.trans hb)).2
  subst bodyB
  rw [oa, ob, fa.unique fb]

theorem quote_iff (s : String) (bytes : List UInt8) :
    Denotes (CTree.quote s).toList bytes ↔ bytes = s.toUTF8.data.toList ++ [0] := by
  constructor
  · intro h; exact denotes_unique h (quote_correct s)
  · intro h; rw [h]; exact quote_correct s

/-- The physical source uses only printable ASCII characters. In
particular it contains no physical newline to participate in line splicing. -/
def printableASCII (text : List Char) : Bool :=
  text.all fun c => 32 ≤ c.toNat && c.toNat ≤ 126

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem byte_ascii : ∀ b : UInt8, printableASCII (CTree.quoteByte b).toList = true := by
  have finite : ∀ n : Fin 256, printableASCII (CTree.quoteByte (UInt8.ofNat n.val)).toList = true := by
    decide +kernel
  intro b
  simpa using finite ⟨b.toNat, b.toNat_lt_size⟩

theorem ascii_append (a b : List Char) :
    printableASCII (a ++ b) = (printableASCII a && printableASCII b) :=
  List.all_append

theorem encoded_ascii (bytes : List UInt8) :
    printableASCII ((bytes.map CTree.quoteByte).flatMap String.toList) = true := by
  induction bytes with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, List.flatMap_cons, ascii_append, byte_ascii, ih, Bool.true_and]

theorem quote_ascii (s : String) : printableASCII (CTree.quote s).toList = true := by
  simp only [CTree.quote, String.toList_append, join_toList, ascii_append]
  change ((true && printableASCII ((s.toUTF8.data.toList.map CTree.quoteByte).flatMap String.toList)) && true) = true
  rw [encoded_ascii]
  rfl

/-- C11 N1570 5.2.1.1's nine trigraph replacements. -/
def trigraph : Char → Option Char
  | '=' => some '#' | '(' => some '[' | '/' => some '\\'
  | ')' => some ']' | '\'' => some '^' | '<' => some '{'
  | '!' => some '|' | '>' => some '}' | '-' => some '~'
  | _ => none

/-- The two character rewrites preceding C tokenization. Permitting them in
any context and any order is stronger than the required phase ordering. -/
inductive Rewrite : List Char → List Char → Prop
  | trigraph (before after : List Char) (c replacement : Char)
      (found : trigraph c = some replacement) :
      Rewrite (before ++ '?' :: '?' :: c :: after) (before ++ replacement :: after)
  | splice (before after : List Char) :
      Rewrite (before ++ '\\' :: '\n' :: after) (before ++ after)

theorem no_rewrite (text out : List Char) (safe : safeFrom false text = true)
    (ascii : printableASCII text = true) : ¬ Rewrite text out := by
  intro step
  cases step with
  | trigraph before after c replacement found =>
    simp [safe_append, safeFrom] at safe
  | splice before after =>
    simp [printableASCII, List.all_append] at ascii

theorem quote_preprocessed (s : String) (out : List Char)
    (steps : Relation.ReflTransGen Rewrite (CTree.quote s).toList out) : out = (CTree.quote s).toList := by
  induction steps with
  | refl => rfl
  | tail path step ih =>
    rw [ih] at step
    exact False.elim (no_rewrite _ _ (quote_safe s) (quote_ascii s) step)

/-- Exact object bytes after any allowed preprocessing rewrites and any
literal interpretation. The equivalence also establishes that decoding exists.
This is a literal contract under the eight-bit ASCII C profile, not a contract
for surrounding declarations, headers, storage addresses or the whole file. -/
def CorrectLiteral (source : String) (text : List Char) : Prop :=
  printableASCII text = true ∧ ∀ processed, Relation.ReflTransGen Rewrite text processed →
    ∀ bytes, Denotes processed bytes ↔ bytes = source.toUTF8.data.toList ++ [0]

theorem quote_contract (s : String) : CorrectLiteral s (CTree.quote s).toList := by
  refine ⟨quote_ascii s, ?_⟩
  intro processed steps bytes
  rw [quote_preprocessed s processed steps]
  exact quote_iff s bytes


/-- The actual string-expression printer satisfies the complete literal
contract. No producer-supplied semantic interpretation is assumed. -/
theorem render_correct (s : String) :
    CorrectLiteral s (CTree.Expr.render (.str s)).toList := by
  simpa only [CTree.Expr.render] using quote_contract s

end Rumoca.CString
