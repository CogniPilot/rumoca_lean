import RumocaC.LiteralDeclaration

/-! Independent complete text contract for a list of static character-array
declarations. Physical newlines separate declarations; payload newlines stay
escaped inside each literal. This closes the inter-declaration boundary for
trigraph replacement and line splicing, not macros or native object layout. -/
namespace Rumoca.CLiteral.Declaration
variable {reserved : List String}

def renderBlock (entries : List Entry) : String :=
  String.join (entries.map fun entry => render entry ++ "\n")

def objects (entries : List Entry) : List (String × List UInt8) :=
  entries.map fun entry => (entry.name, bytes entry.text)

/-- Independent declaration syntax, with one terminated physical line per
object. Both the whole source and the whole declaration sequence are covered. -/
def BlockDenotes (reserved : List String) : List Char → List (String × List UInt8) → Prop
  | text, [] => text = []
  | text, (name, object) :: rest =>
      ∃ line remaining, text = line ++ '\n' :: remaining ∧ '\n' ∉ line ∧
        Denotes reserved line name object ∧ BlockDenotes reserved remaining rest

private theorem before_newline (line rest : List Char) (absent : '\n' ∉ line) :
    (line ++ '\n' :: rest).takeWhile (· != '\n') = line := by
  induction line with
  | nil => simp
  | cons c cs ih =>
      have different : c ≠ '\n' := fun same => absent (by simp [same])
      have tailFree : '\n' ∉ cs := fun member => absent (List.mem_cons_of_mem _ member)
      simp [different, ih tailFree]

private theorem split_unique {line₁ rest₁ line₂ rest₂ : List Char}
    (first : '\n' ∉ line₁) (second : '\n' ∉ line₂)
    (same : line₁ ++ '\n' :: rest₁ = line₂ ++ '\n' :: rest₂) :
    line₁ = line₂ ∧ rest₁ = rest₂ := by
  have lines := congrArg (List.takeWhile (· != '\n')) same
  rw [before_newline _ _ first, before_newline _ _ second] at lines
  subst line₂
  exact ⟨rfl, (List.cons.inj (List.append_cancel_left same)).2⟩

theorem block_unique (first : BlockDenotes reserved text a)
    (second : BlockDenotes reserved text b) : a = b := by
  induction a generalizing text b with
  | nil =>
      cases b with
      | nil => rfl
      | cons object rest =>
          obtain ⟨line, remaining, same, _⟩ := second
          simp only [BlockDenotes] at first
          rw [first] at same
          have lengths := congrArg List.length same
          simp at lengths
  | cons object rest ih =>
      obtain ⟨line, remaining, same, absent, declared, tail⟩ := first
      cases b with
      | nil =>
          simp only [BlockDenotes] at second
          rw [second] at same
          have lengths := congrArg List.length same
          simp at lengths
      | cons object₂ rest₂ =>
          obtain ⟨line₂, remaining₂, same₂, absent₂, declared₂, tail₂⟩ := second
          obtain ⟨rfl, rfl⟩ := split_unique absent absent₂ (same.symm.trans same₂)
          have components := denotes_unique declared declared₂
          have sameObject : object = object₂ := Prod.ext components.1 components.2
          exact congrArg₂ List.cons sameObject (ih tail tail₂)

theorem renderBlock_chars (entries : List Entry) :
    (renderBlock entries).toList = entries.flatMap (fun entry => (render entry).toList ++ ['\n']) := by
  simp [renderBlock, CString.join_toList, List.flatMap_map, String.toList_append]

private theorem ascii_no_newline (ascii : CString.printableASCII text = true) : '\n' ∉ text := by
  intro member
  have bounds := List.all_eq_true.mp ascii '\n' member
  contradiction

theorem renderBlock_denotes (entries : List Entry)
    (valid : ∀ entry ∈ entries, CIdentifier.valid reserved entry.name = true) :
    BlockDenotes reserved (renderBlock entries).toList (objects entries) := by
  rw [renderBlock_chars]
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      refine ⟨(render entry).toList, rest.flatMap (fun e => (render e).toList ++ ['\n']),
        by simp, ascii_no_newline (render_ascii entry (valid entry (by simp))),
        render_denotes entry (valid entry (by simp)), ?_⟩
      exact ih (fun entry member => valid entry (List.mem_cons_of_mem _ member))

/-- Detect the C11 phase-2 splice pair even across adjacent source fragments. -/
def spliceFreeFrom : Bool → List Char → Bool
  | _, [] => true
  | previous, c :: rest => !(previous && c == '\n') && spliceFreeFrom (c == '\\') rest

def endBackslash (text : List Char) (previous : Bool) : Bool :=
  text.foldl (fun _ c => c == '\\') previous

theorem splice_append (left right : List Char) (previous : Bool) :
    spliceFreeFrom previous (left ++ right) =
      (spliceFreeFrom previous left && spliceFreeFrom (endBackslash left previous) right) := by
  induction left generalizing previous with
  | nil => simp [spliceFreeFrom, endBackslash]
  | cons c cs ih => simp [spliceFreeFrom, endBackslash, ih, Bool.and_assoc]

private theorem splice_ascii (text : List Char) (ascii : CString.printableASCII text = true)
    (previous : Bool) : spliceFreeFrom previous text = true := by
  induction text generalizing previous with
  | nil => rfl
  | cons c cs ih =>
      have absent := ascii_no_newline ascii
      have different : c ≠ '\n' := fun same => absent (by simp [same])
      have tailASCII : CString.printableASCII cs = true := by
        apply List.all_eq_true.mpr
        intro a member
        exact List.all_eq_true.mp ascii a (List.mem_cons_of_mem _ member)
      simp [spliceFreeFrom, different, ih tailASCII]

private theorem render_safe_any (entry : Entry) (valid : CIdentifier.valid reserved entry.name = true)
    (previous : Bool) : CString.safeFrom previous (render entry).toList = true := by
  simpa [render, String.toList_append, CString.safeFrom] using render_safe entry valid

theorem renderBlock_safe (entries : List Entry)
    (valid : ∀ entry ∈ entries, CIdentifier.valid reserved entry.name = true) (previous : Bool) :
    CString.safeFrom previous (renderBlock entries).toList = true ∧
      spliceFreeFrom previous (renderBlock entries).toList = true := by
  rw [renderBlock_chars]
  induction entries generalizing previous with
  | nil => exact ⟨rfl, rfl⟩
  | cons entry rest ih =>
      have good := valid entry (by simp)
      have tails := ih (fun e member => valid e (List.mem_cons_of_mem _ member)) false
      have endSlash : endBackslash (render entry).toList previous = false := by
        simp [render, String.toList_append, endBackslash, List.foldl_append]
      constructor
      · simp [List.append_assoc, CString.safe_append, render_safe_any entry good,
          CString.safeFrom, tails.1]
      · simp [List.append_assoc, splice_append, splice_ascii _ (render_ascii entry good),
          endSlash, spliceFreeFrom, tails.2]

private theorem block_no_rewrite (text output : List Char)
    (safe : CString.safeFrom false text = true) (splice : spliceFreeFrom false text = true) :
    ¬ CString.Rewrite text output := by
  intro step
  cases step with
  | trigraph before after c replacement found =>
      simp [CString.safe_append, CString.safeFrom] at safe
  | splice before after =>
      simp [splice_append, spliceFreeFrom] at splice

theorem renderBlock_preprocessed (entries : List Entry)
    (valid : ∀ entry ∈ entries, CIdentifier.valid reserved entry.name = true)
    (steps : Relation.ReflTransGen CString.Rewrite (renderBlock entries).toList processed) :
    processed = (renderBlock entries).toList := by
  induction steps with
  | refl => rfl
  | tail path step ih =>
      rw [ih] at step
      have safe := renderBlock_safe entries valid false
      exact False.elim (block_no_rewrite _ _ safe.1 safe.2 step)

def BlockCorrect (reserved : List String) (entries : List Entry) (text : List Char) : Prop :=
  ∀ processed, Relation.ReflTransGen CString.Rewrite text processed →
    ∀ initialized, BlockDenotes reserved processed initialized ↔ initialized = objects entries

theorem renderBlock_correct (entries : List Entry)
    (valid : ∀ entry ∈ entries, CIdentifier.valid reserved entry.name = true) :
    BlockCorrect reserved entries (renderBlock entries).toList := by
  intro processed steps initialized
  rw [renderBlock_preprocessed entries valid steps]
  constructor
  · intro interpreted
    exact block_unique interpreted (renderBlock_denotes entries valid)
  · rintro rfl
    exact renderBlock_denotes entries valid

/-- Every independently interpreted declaration names its actual constructed
symbolic array, with all initializer bytes including the terminator. This
connects the text sequence to named lookup and storage; native layout and
freshness against pre-existing objects remain separate obligations. -/
theorem renderBlock_storage (pool : Pool reserved) (before : CMemory.Heap)
    (firstBlock : Nat) (signed : Bool)
    (interpreted : BlockDenotes ("isfinite" :: reserved)
      (renderBlock pool.entries).toList initialized)
    (member : (name, object) ∈ initialized) :
    ∃ address,
      pool.globals firstBlock name = some (.pointer (some address)) ∧
      ∀ index byte, object[index]? = some byte →
        readByte (pool.install before firstBlock signed) (address.index index) = some byte := by
  have exactObjects := block_unique interpreted
    (renderBlock_denotes pool.entries (fun _ h => (pool.entry_valid h).1))
  rw [exactObjects] at member
  obtain ⟨entry, inPool, same⟩ := List.mem_map.mp member
  cases same
  refine ⟨entry.address firstBlock, ?_, ?_⟩
  · have binding := pool.global_binding firstBlock (pool.symbol_of_mem inPool)
    simpa only [pool.address_of_mem firstBlock inPool, Option.map_some] using binding
  · intro index byte found
    exact (pool.installed before firstBlock signed inPool).read_byte found

end Rumoca.CLiteral.Declaration
