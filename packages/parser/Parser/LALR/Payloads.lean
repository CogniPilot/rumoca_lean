import Parser.LALR.Actions

/-! Payload attachment for an existing CST. Terminal encodings need not be
injective: every leaf keeps the original payload. Attachment checks only leaf
alignment, not grammar validity; the existing checked parser supplies validity.
No lexer, grammar or parser execution path is changed by this module. -/
namespace Parser.LALR

inductive PayloadTree (α : Type) where
  | terminal (payload : α)
  | node (production nonterminal : Nat) (children : List (PayloadTree α))

namespace PayloadTree

def erase (encode : α → Nat) : PayloadTree α → Tree
  | .terminal a => .terminal (encode a)
  | .node p n cs => .node p n (cs.map (erase encode))
  termination_by t => sizeOf t

/-- Accumulator leaf traversal; no subtree yields are repeatedly appended. -/
def prependTokens : PayloadTree α → List α → List α
  | .terminal a, tail => a :: tail
  | .node _ _ cs, tail => cs.foldr prependTokens tail
  termination_by t _ => sizeOf t

theorem prependTokens_append (tree : PayloadTree α) :
    ∀ xs ys, tree.prependTokens (xs ++ ys) = tree.prependTokens xs ++ ys := by
  refine PayloadTree.rec
    (motive_1 := fun t => ∀ xs ys, t.prependTokens (xs ++ ys) = t.prependTokens xs ++ ys)
    (motive_2 := fun cs => ∀ xs ys,
      cs.foldr prependTokens (xs ++ ys) = cs.foldr prependTokens xs ++ ys)
    ?_ ?_ ?_ ?_ tree
  · intro a xs ys; simp only [prependTokens, List.cons_append]
  · intro p n cs ih xs ys; simpa only [prependTokens] using ih xs ys
  · intro xs ys; rfl
  · intro c cs ih ir xs ys
    simp only [List.foldr_cons, ir, ih]

theorem erase_word (encode : α → Nat) (tree : PayloadTree α) :
    ∀ tail, (tree.erase encode).word ++ tail.map encode =
      (tree.prependTokens tail).map encode := by
  refine PayloadTree.rec
    (motive_1 := fun t => ∀ tail, (t.erase encode).word ++ tail.map encode =
      (t.prependTokens tail).map encode)
    (motive_2 := fun cs => ∀ tail,
      ((cs.map (erase encode)).flatMap Tree.word) ++ tail.map encode =
        (cs.foldr prependTokens tail).map encode) ?_ ?_ ?_ ?_ tree
  · intro a tail; simp only [erase, Tree.word, prependTokens, List.singleton_append, List.map_cons]
  · intro p n cs ih tail; simpa only [erase, Tree.word, prependTokens] using ih tail
  · intro tail; rfl
  · intro c cs ih ir tail
    simp only [List.map_cons, List.flatMap_cons, List.append_assoc, ir, ih, List.foldr_cons]

mutual
  /-- Consume exactly the leaves of one tree, retaining the unused suffix. -/
  def attachPrefix (encode : α → Nat) (tree : Tree) (tokens : List α) :
      Option (PayloadTree α × List α) :=
    match tree with
    | .terminal t => match tokens with
      | [] => none
      | a :: rest => if encode a = t then some (.terminal a, rest) else none
    | .node p n cs => do
      let (children, rest) ← attachForest encode cs tokens
      return (.node p n children, rest)
    termination_by sizeOf tree

  def attachForest (encode : α → Nat) (trees : List Tree) (tokens : List α) :
      Option (List (PayloadTree α) × List α) :=
    match trees with
    | [] => some ([], tokens)
    | t :: ts => do
      let (child, rest) ← attachPrefix encode t tokens
      let (children, suffix) ← attachForest encode ts rest
      return (child :: children, suffix)
    termination_by sizeOf trees
end

/-- Exact structure and consumed-prefix/remaining-suffix invariant. -/
theorem attachPrefix_sound (encode : α → Nat) (tree : Tree) :
    ∀ tokens payload rest, attachPrefix encode tree tokens = some (payload, rest) →
      payload.erase encode = tree ∧ payload.prependTokens rest = tokens := by
  refine Tree.rec
    (motive_1 := fun t => ∀ tokens payload rest,
      attachPrefix encode t tokens = some (payload, rest) →
        payload.erase encode = t ∧ payload.prependTokens rest = tokens)
    (motive_2 := fun cs => ∀ tokens payloads rest,
      attachForest encode cs tokens = some (payloads, rest) →
        payloads.map (erase encode) = cs ∧ payloads.foldr prependTokens rest = tokens)
    ?_ ?_ ?_ ?_ tree
  · intro t tokens payload rest h
    cases tokens with
    | nil => simp [attachPrefix] at h
    | cons a tail =>
      simp only [attachPrefix] at h
      split at h
      · cases Option.some.inj h
        exact ⟨by simp [erase, *], by simp [prependTokens]⟩
      · contradiction
  · intro p n cs ih tokens payload rest h
    cases hf : attachForest encode cs tokens with
    | none => simp [attachPrefix, hf] at h
    | some result =>
      obtain ⟨children, suffix⟩ := result
      simp [attachPrefix, hf] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨he, hl⟩ := ih _ _ _ hf
      exact ⟨by simpa only [erase] using congrArg (Tree.node p n) he,
        by simpa only [prependTokens] using hl⟩
  · intro tokens payloads rest h
    simp only [attachForest] at h
    cases Option.some.inj h
    exact ⟨rfl, rfl⟩
  · intro c cs ih ir tokens payloads rest h
    cases hc : attachPrefix encode c tokens with
    | none => simp [attachForest, hc] at h
    | some result =>
      obtain ⟨child, middle⟩ := result
      cases hr : attachForest encode cs middle with
      | none => simp [attachForest, hc, hr] at h
      | some result =>
        obtain ⟨children, suffix⟩ := result
        simp [attachForest, hc, hr] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨he, hl⟩ := ih _ _ _ hc
        obtain ⟨hes, hls⟩ := ir _ _ _ hr
        exact ⟨by simp [he, hes], by simpa only [List.foldr_cons, hls] using hl⟩

/-- Every matching payload prefix can be attached, with its suffix untouched. -/
theorem attachPrefix_complete (encode : α → Nat) (tree : Tree) :
    ∀ front suffix, tree.word = front.map encode →
      ∃ payload, attachPrefix encode tree (front ++ suffix) = some (payload, suffix) := by
  refine Tree.rec
    (motive_1 := fun t => ∀ front suffix, t.word = front.map encode →
      ∃ payload, attachPrefix encode t (front ++ suffix) = some (payload, suffix))
    (motive_2 := fun cs => ∀ front suffix, cs.flatMap Tree.word = front.map encode →
      ∃ payloads, attachForest encode cs (front ++ suffix) = some (payloads, suffix))
    ?_ ?_ ?_ ?_ tree
  · intro t front suffix h
    cases front with
    | nil => simp [Tree.word] at h
    | cons a tail =>
      simp only [Tree.word, List.map_cons, List.cons.injEq] at h
      obtain ⟨ht, hr⟩ := h
      have empty : tail = [] := List.map_eq_nil_iff.mp hr.symm
      subst tail
      exact ⟨.terminal a, by simp [attachPrefix, ht]⟩
  · intro p n cs ih front suffix h
    obtain ⟨children, hc⟩ := ih front suffix (by simpa only [Tree.word] using h)
    exact ⟨.node p n children, by simp [attachPrefix, hc]⟩
  · intro front suffix h
    have empty : front = [] := List.map_eq_nil_iff.mp h.symm
    subst front
    exact ⟨[], by simp [attachForest]⟩
  · intro c cs ih ir front suffix h
    have hh : c.word = (front.take c.word.length).map encode := by
      rw [List.map_take, ← h]
      simp
    have ht : cs.flatMap Tree.word = (front.drop c.word.length).map encode := by
      rw [List.map_drop, ← h]
      simp
    obtain ⟨child, hc⟩ := ih _ (front.drop c.word.length ++ suffix) hh
    obtain ⟨children, hr⟩ := ir _ suffix ht
    refine ⟨child :: children, ?_⟩
    have splitPrefix : front ++ suffix =
        front.take c.word.length ++ (front.drop c.word.length ++ suffix) := by
      rw [← List.append_assoc, List.take_append_drop]
    rw [splitPrefix]
    simp [attachForest, hc, hr]

/-- Attach all input payloads; a nonempty leftover is a rejection. -/
def attach (encode : α → Nat) (tree : Tree) (tokens : List α) : Option (PayloadTree α) := do
  let (payload, rest) ← attachPrefix encode tree tokens
  match rest with
  | [] => some payload
  | _ :: _ => none

theorem attach_sound (encode : α → Nat) (tree : Tree) (tokens : List α)
    (h : attach encode tree tokens = some payload) :
    payload.erase encode = tree ∧ payload.prependTokens [] = tokens := by
  cases hw : attachPrefix encode tree tokens with
  | none => simp [attach, hw] at h
  | some result =>
    obtain ⟨p, rest⟩ := result
    cases rest with
    | cons a rest => simp [attach, hw] at h
    | nil =>
      simp only [attach, hw] at h
      cases Option.some.inj h
      exact attachPrefix_sound encode tree tokens _ [] hw

theorem attach_iff (encode : α → Nat) (tree : Tree) (tokens : List α) :
    (∃ payload, attach encode tree tokens = some payload) ↔ tree.word = tokens.map encode := by
  constructor
  · rintro ⟨payload, h⟩
    obtain ⟨he, hl⟩ := attach_sound encode tree tokens h
    simpa only [he, hl, List.map_nil, List.append_nil] using payload.erase_word encode []
  · intro h
    obtain ⟨payload, hp⟩ := attachPrefix_complete encode tree tokens [] h
    simp only [List.append_nil] at hp
    exact ⟨payload, by simp [attach, hp]⟩

/-- Exact erasure transfers the existing checker, without a new validity test. -/
theorem attach_checked (encode : α → Nat) (tree : Tree) (tokens : List α)
    (h : attach encode tree tokens = some payload)
    (checked : checkTree grammar (tokens.map encode) tree = true) :
    checkTree grammar (tokens.map encode) (payload.erase encode) = true := by
  rw [(attach_sound encode tree tokens h).1]
  exact checked

end PayloadTree

/-- Any successful existing token parse admits exact payload attachment. -/
theorem TokenParser.attach_total (parser : TokenParser α)
    (parsed : parser.run tokens = .ok tree) :
    ∃ payload, PayloadTree.attach parser.encode tree tokens = some payload ∧
      payload.erase parser.encode = tree ∧ payload.prependTokens [] = tokens ∧
      checkTree parser.grammar (tokens.map parser.encode) (payload.erase parser.encode) = true := by
  have checked := parser.checked tokens tree parsed
  obtain ⟨payload, h⟩ := (PayloadTree.attach_iff parser.encode tree tokens).mpr
    (checkTree_sound _ _ _ checked).1
  obtain ⟨he, hl⟩ := PayloadTree.attach_sound parser.encode tree tokens h
  exact ⟨payload, h, he, hl, PayloadTree.attach_checked parser.encode tree tokens h checked⟩

end Parser.LALR
