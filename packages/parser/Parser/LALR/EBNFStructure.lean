import Parser.LALR.Payloads
import Parser.LALR.EBNFSoundness

/-! Structural interpretation of actual payload CSTs. Runtime annotations are
ordinary data; a lowering witness is used only in the correctness theorems.
Helpers are identified by their meanings, not by allocation freshness. -/
namespace Parser.LALR.Frontend.Structure

/-- A finite realization of the existing EBNF expressions. Repetitions retain
each cons, including occurrences whose body has no leaves. -/
inductive Value (α : Type) where
  | empty
  | terminal (symbol : Parser.Symbol) (payload : α)
  | named (name : String) (body : Value α)
  | seq (left right : Value α)
  | altLeft (right : EBNF.Expr) (body : Value α)
  | altRight (left : EBNF.Expr) (body : Value α)
  | optionalEmpty (body : EBNF.Expr)
  | optionalSome (body : Value α)
  | manyEmpty (body : EBNF.Expr)
  | manyCons (head tail : Value α)

def Value.expr : Value α → EBNF.Expr
  | .empty => .terminal (.literal "")
  | .terminal s _ => .terminal s
  | .named name _ => .ref name
  | .seq a b => .seq a.expr b.expr
  | .altLeft b a => .alt a.expr b
  | .altRight a b => .alt a b.expr
  | .optionalEmpty a => .optional a
  | .optionalSome a => .optional a.expr
  | .manyEmpty a => .many a
  | .manyCons a _ => .many a.expr

def Value.tokens : Value α → List α
  | .empty | .optionalEmpty _ | .manyEmpty _ => []
  | .terminal _ a => [a]
  | .named _ a | .altLeft _ a | .altRight _ a | .optionalSome a => a.tokens
  | .seq a b | .manyCons a b => a.tokens ++ b.tokens

/-- Accumulator traversal for payload and diagnostic consumers. -/
def Value.prependTokens : Value α → List α → List α
  | .empty, tail | .optionalEmpty _, tail | .manyEmpty _, tail => tail
  | .terminal _ a, tail => a :: tail
  | .named _ a, tail | .altLeft _ a, tail | .altRight _ a, tail
  | .optionalSome a, tail => a.prependTokens tail
  | .seq a b, tail | .manyCons a b, tail => a.prependTokens (b.prependTokens tail)

theorem Value.prependTokens_eq (v : Value α) (tail : List α) :
    v.prependTokens tail = v.tokens ++ tail := by
  induction v generalizing tail <;> simp_all [prependTokens, tokens, List.append_assoc]

abbrev Cell (α : Type) := Atom × Value α

variable {α : Type}

def leaves (cs : List (Cell α)) : List α := cs.flatMap (fun c => c.2.tokens)

def takeCell (symbol : Atom) (expr : EBNF.Expr) :
    List (Cell α) → Option (Value α × List (Cell α))
  | [] => none
  | (s, v) :: rest => if s = symbol ∧ v.expr = expr then some (v, rest) else none

/-- Inline interpretation consumes the actual converted children. In particular
an alternative does not rerun either branch on the token word. -/
def read (f : Fragment) (cs : List (Cell α)) : Option (Value α × List (Cell α)) :=
  match f with
  | .empty => some (.empty, cs)
  | .terminal s t => takeCell (.terminal t) (.terminal s) cs
  | .ref name n => takeCell (.nonterminal n) (.ref name) cs
  | .alt n a b => takeCell (.nonterminal n) (.alt a.expr b.expr) cs
  | .optional n a => takeCell (.nonterminal n) (.optional a.expr) cs
  | .many n a => takeCell (.nonterminal n) (.many a.expr) cs
  | .seq a b => do
    let (left, rest) ← read a cs
    let (right, suffix) ← read b rest
    return (.seq left right, suffix)

/-- Independent local structural relation: sequences assemble their two actual
readings; an atomic fragment retains the exact child value. -/
def Atomic : Fragment → Prop
  | .empty | .seq _ _ => False
  | _ => True

inductive Reads : Fragment → List (Cell α) → Value α → List (Cell α) → Prop where
  | empty : Reads .empty cs .empty cs
  | atom (atomic : Atomic f) (rhs : f.rhs = [s]) (expr : v.expr = f.expr) :
      Reads f ((s, v) :: rest) v rest
  | seq (left : Reads a cs x middle) (right : Reads b middle y rest) :
      Reads (.seq a b) cs (.seq x y) rest

section
variable {cs rest : List (Cell α)} {v : Value α}

theorem takeCell_iff : takeCell s e cs = some (v, rest) ↔
    cs = (s, v) :: rest ∧ v.expr = e := by
  cases cs with
  | nil => simp [takeCell]
  | cons c cs =>
    obtain ⟨a, b⟩ := c
    simp only [takeCell]
    split
    · rename_i h
      obtain ⟨rfl, he⟩ := h
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, Prod.mk.injEq,
        true_and]
      constructor
      · rintro ⟨rfl, rfl⟩; exact ⟨⟨rfl, rfl⟩, he⟩
      · rintro ⟨⟨rfl, rfl⟩, _⟩; exact ⟨rfl, rfl⟩
    · rename_i h
      constructor
      · intro bad; contradiction
      · rintro ⟨hc, he⟩
        obtain ⟨hab, _⟩ := List.cons.inj hc
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hab
        exact False.elim (h ⟨rfl, he⟩)

theorem read_sound (f : Fragment) : ∀ (cs : List (Cell α)) v rest,
    read f cs = some (v, rest) → Reads f cs v rest := by
  induction f with
  | empty => intro cs v rest h; cases Option.some.inj h; exact .empty
  | terminal s t | ref s t =>
    intro cs v rest h
    obtain ⟨rfl, he⟩ := takeCell_iff.mp h
    exact .atom trivial rfl he
  | alt n a b _ _ | optional n a _ | many n a _ =>
    intro cs v rest h
    obtain ⟨rfl, he⟩ := takeCell_iff.mp h
    exact .atom trivial rfl he
  | seq a b ia ib =>
    intro cs v rest h
    cases ha : read a cs with
    | none => simp [read, ha] at h
    | some result =>
      obtain ⟨x, middle⟩ := result
      cases hb : read b middle with
      | none => simp [read, ha, hb] at h
      | some result =>
        obtain ⟨y, suffix⟩ := result
        simp [read, ha, hb] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .seq (ia _ _ _ ha) (ib _ _ _ hb)

/-- Exact consumed child prefix, unused suffix, expression and original payloads. -/
theorem Reads.exact (h : Reads f cs v rest) :
    v.expr = f.expr ∧ ∃ pre, cs = pre ++ rest ∧
      pre.map Prod.fst = f.rhs ∧ v.tokens = leaves pre := by
  induction h with
  | empty => exact ⟨rfl, [], rfl, rfl, rfl⟩
  | atom _ rhs expr => exact ⟨expr, [_], rfl, rhs.symm, by simp [leaves]⟩
  | seq _ _ ih ih' =>
    obtain ⟨hx, pre, rfl, hp, ht⟩ := ih
    obtain ⟨hy, pre', rfl, hp', ht'⟩ := ih'
    exact ⟨by simp [Value.expr, Fragment.expr, hx, hy], pre ++ pre',
      (List.append_assoc ..).symm, by simp [Fragment.rhs, hp, hp'],
      by simp [Value.tokens, leaves, ht, ht']⟩

def finish (result : Option (Value α × List (Cell α))) : Option (Value α) := do
  let (v, rest) ← result
  match rest with
  | [] => some v
  | _ :: _ => none

theorem finish_iff {result : Option (Value α × List (Cell α))} :
    finish result = some v ↔ result = some (v, []) := by
  cases result with
  | none => simp [finish]
  | some r =>
    obtain ⟨x, xs⟩ := r
    cases xs <;> simp [finish]

theorem Reads.run (h : Reads f cs v rest) : read f cs = some (v, rest) := by
  induction h with
  | empty => rfl
  | @atom f s v rest atomic rhs expr =>
    cases f <;> simp only [Atomic] at atomic
    all_goals simp only [Fragment.rhs, List.singleton_inj] at rhs
    all_goals subst s
    all_goals exact takeCell_iff.mpr ⟨rfl, expr⟩
  | seq _ _ ih ih' => simp [read, ih, ih']

theorem read_iff : read f cs = some (v, rest) ↔ Reads f cs v rest :=
  ⟨read_sound f cs v rest, Reads.run⟩

/-- The annotation chooses the constructor, even when two branches have the
same word or a nullable repetition body consumes no terminals. -/
def applyRule (rule : AnnotatedRule) (cs : List (Cell α)) : Option (Value α) :=
  match rule with
  | .named _ name body => (finish (read body cs)).map (.named name)
  | .altLeft _ a b => (finish (read a cs)).map (.altLeft b.expr)
  | .altRight _ a b => (finish (read b cs)).map (.altRight a.expr)
  | .optionalSome _ a => (finish (read a cs)).map .optionalSome
  | .optionalEmpty _ a => if cs.isEmpty then some (.optionalEmpty a.expr) else none
  | .manyEmpty _ a => if cs.isEmpty then some (.manyEmpty a.expr) else none
  | .manyCons n a => do
    let (head, rest) ← read a cs
    let tail ← finish (takeCell (.nonterminal n) (.many a.expr) rest)
    return .manyCons head tail

end

/-- Exact annotation fidelity, independent of the executable. -/
inductive Applies : AnnotatedRule → List (Cell α) → Value α → Prop where
  | named (h : Reads a cs v []) : Applies (.named n name a) cs (.named name v)
  | altLeft (h : Reads a cs v []) : Applies (.altLeft n a b) cs (.altLeft b.expr v)
  | altRight (h : Reads b cs v []) : Applies (.altRight n a b) cs (.altRight a.expr v)
  | optionalEmpty : Applies (.optionalEmpty n a) [] (.optionalEmpty a.expr)
  | optionalSome (h : Reads a cs v []) : Applies (.optionalSome n a) cs (.optionalSome v)
  | manyEmpty : Applies (.manyEmpty n a) [] (.manyEmpty a.expr)
  | manyCons (h : Reads a cs x [(.nonterminal n, y)]) (tail : y.expr = .many a.expr) :
      Applies (.manyCons n a) cs (.manyCons x y)

section
variable {cs rest : List (Cell α)} {v : Value α}

theorem applyRule_iff {r : AnnotatedRule} : applyRule r cs = some v ↔ Applies r cs v := by
  cases r with
  | named n name a | altLeft n a b | altRight n a b | optionalSome n a =>
    simp only [applyRule, Option.map_eq_some_iff, finish_iff, read_iff]
    constructor
    · rintro ⟨x, h, rfl⟩; constructor; exact h
    · intro h; cases h; exact ⟨_, ‹Reads _ _ _ _›, rfl⟩
  | optionalEmpty n a | manyEmpty n a =>
    cases cs with
    | nil =>
      simp only [applyRule, List.isEmpty_nil, ↓reduceIte, Option.some.injEq]
      constructor
      · rintro rfl; constructor
      · intro h; cases h; rfl
    | cons c cs =>
      simp only [applyRule, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro h; contradiction
      · intro h; cases h
  | manyCons n a =>
    constructor
    · intro h
      cases hr : read a cs with
      | none => simp [applyRule, hr] at h
      | some pair =>
        obtain ⟨x, rest⟩ := pair
        cases ht : finish (takeCell (.nonterminal n) (.many a.expr) rest) with
        | none => simp [applyRule, hr, ht] at h
        | some y =>
          simp [applyRule, hr, ht] at h
          subst v
          obtain ⟨rfl, he⟩ := takeCell_iff.mp (finish_iff.mp ht)
          exact .manyCons (read_iff.mp hr) he
    · intro h
      cases h with
      | manyCons hr he =>
        have ht := finish_iff.mpr (takeCell_iff (s := .nonterminal n) |>.mpr ⟨rfl, he⟩)
        simp [applyRule, hr.run, ht]

theorem Reads.leaves (h : Reads f cs v rest) :
    v.tokens ++ leaves rest = leaves cs := by
  obtain ⟨_, pre, rfl, _, ht⟩ := h.exact
  simp [ht, Structure.leaves]

theorem Applies.exact (h : Applies r cs v) :
    v.expr = r.meaning ∧ v.tokens = leaves cs := by
  cases h with
  | named h | altLeft h | altRight h | optionalSome h =>
    exact ⟨by simp [Value.expr, AnnotatedRule.meaning, h.exact.1],
      by simpa only [Value.tokens, leaves, List.flatMap_nil, List.append_nil] using h.leaves⟩
  | optionalEmpty | manyEmpty => exact ⟨rfl, rfl⟩
  | manyCons h he =>
    exact ⟨by simp [Value.expr, AnnotatedRule.meaning, h.exact.1],
      by simpa only [Value.tokens, leaves, List.flatMap_cons, List.flatMap_nil,
        List.append_nil] using h.leaves⟩

end

def Fits (p : Prepared) (meanings : Meanings) (c : Cell α) : Prop :=
  match c.1 with
  | .terminal t => c.2.expr = .terminal (p.decode t)
  | .nonterminal n => meanings[n]? = some c.2.expr

/-- Total local reading for every forest with the fragment's actual symbols
and certified meanings. The arbitrary suffix is returned untouched. -/
theorem read_total (f : Fragment) (interprets : f.Interprets p meanings)
    (front suffix : List (Cell α)) (symbols : front.map Prod.fst = f.rhs)
    (fits : ∀ c ∈ front, Fits p meanings c) :
    ∃ v, read f (front ++ suffix) = some (v, suffix) := by
  induction f generalizing front suffix with
  | empty =>
    have h : front = [] := List.map_eq_nil_iff.mp symbols
    subst front
    exact ⟨.empty, rfl⟩
  | seq a b ia ib =>
    obtain ⟨xs, ys, rfl, hx, hy⟩ := List.map_eq_append_iff.mp symbols
    obtain ⟨x, hrx⟩ := ia interprets.1 xs (ys ++ suffix) hx
      (fun c hc => fits c (List.mem_append_left _ hc))
    obtain ⟨y, hry⟩ := ib interprets.2 ys suffix hy
      (fun c hc => fits c (List.mem_append_right _ hc))
    exact ⟨.seq x y, by simp [read, List.append_assoc, hrx, hry]⟩
  | terminal s t =>
    obtain ⟨⟨atom, v⟩, tail, rfl, hs, ht⟩ := List.map_eq_cons_iff.mp symbols
    have hnil : tail = [] := List.map_eq_nil_iff.mp ht
    subst tail
    dsimp only at hs
    subst atom
    have hv := fits (.terminal t, v) (by simp)
    have hd : p.decode t = s := by simp [Prepared.decode, interprets.1]
    exact ⟨v, takeCell_iff.mpr ⟨rfl, by simpa [Fits, hd] using hv⟩⟩
  | ref name n | alt n a b _ _ | optional n a _ | many n a _ =>
    obtain ⟨⟨atom, v⟩, tail, rfl, hs, ht⟩ := List.map_eq_cons_iff.mp symbols
    have hnil : tail = [] := List.map_eq_nil_iff.mp ht
    subst tail
    dsimp only at hs
    subst atom
    have hv := fits (.nonterminal n, v) (by simp)
    have he := Option.some.inj (hv.symm.trans interprets)
    exact ⟨v, takeCell_iff.mpr ⟨rfl, he⟩⟩

theorem applyRule_total (r : AnnotatedRule) (valid : r.Valid source p meanings)
    (cs : List (Cell α)) (symbols : cs.map Prod.fst = r.production.output)
    (fits : ∀ c ∈ cs, Fits p meanings c) :
    ∃ v, applyRule r cs = some v := by
  cases r with
  | named n name a =>
    obtain ⟨v, h⟩ := read_total a valid.2.2 cs [] symbols fits
    simp only [List.append_nil] at h
    exact ⟨.named name v, applyRule_iff.mpr (.named (read_iff.mp h))⟩
  | altLeft n a b | altRight n b a | optionalSome n a =>
    obtain ⟨v, h⟩ := read_total a valid.2 cs [] symbols fits
    simp only [List.append_nil] at h
    exact ⟨_, applyRule_iff.mpr (by constructor; exact read_iff.mp h)⟩
  | optionalEmpty n a | manyEmpty n a =>
    have h : cs = [] := List.map_eq_nil_iff.mp symbols
    subst cs
    exact ⟨_, applyRule_iff.mpr (by constructor)⟩
  | manyCons n a =>
    obtain ⟨xs, ys, rfl, hx, hy⟩ := List.map_eq_append_iff.mp symbols
    obtain ⟨⟨atom, tail⟩, zs, rfl, hs, hz⟩ := List.map_eq_cons_iff.mp hy
    have empty : zs = [] := List.map_eq_nil_iff.mp hz
    subst zs
    dsimp only at hs
    subst atom
    have ht := fits (.nonterminal n, tail) (by simp)
    have he : tail.expr = .many a.expr := Option.some.inj (ht.symm.trans valid.1)
    obtain ⟨v, h⟩ := read_total a valid.2 xs [(.nonterminal n, tail)] hx
      (fun c hc => fits c (List.mem_append_left _ hc))
    exact ⟨_, applyRule_iff.mpr (.manyCons (read_iff.mp h) he)⟩

/-- Semantic validity of the recorded realization, including the body chosen
at every named, alternative, optional and repetition node. -/
inductive Valid (source : EBNF.Grammar) (symbol : α → Parser.Symbol) : Value α → Prop where
  | empty : Valid source symbol .empty
  | terminal (same : symbol a = s) (nonempty : s ≠ .literal "") :
      Valid source symbol (.terminal s a)
  | named (rule : (name, v.expr) ∈ source) (body : Valid source symbol v) :
      Valid source symbol (.named name v)
  | seq (left : Valid source symbol x) (right : Valid source symbol y) :
      Valid source symbol (.seq x y)
  | altLeft (body : Valid source symbol v) : Valid source symbol (.altLeft b v)
  | altRight (body : Valid source symbol v) : Valid source symbol (.altRight a v)
  | optionalEmpty : Valid source symbol (.optionalEmpty a)
  | optionalSome (body : Valid source symbol v) : Valid source symbol (.optionalSome v)
  | manyEmpty : Valid source symbol (.manyEmpty a)
  | manyCons (head : Valid source symbol x) (tail : Valid source symbol y)
      (same : y.expr = .many x.expr) : Valid source symbol (.manyCons x y)

/-- Classifier transport is local to the actual retained payloads. -/
theorem Valid.congr (h : Structure.Valid g f v)
    (agree : ∀ t ∈ v.tokens, f t = k t) : Structure.Valid g k v := by
  induction h with
  | empty => exact .empty
  | terminal same nonempty =>
    exact .terminal ((agree _ (by simp [Structure.Value.tokens])).symm.trans same) nonempty
  | named rule _ ih => exact .named rule (ih agree)
  | seq _ _ ih ih' =>
    exact .seq (ih (fun t ht => agree t (List.mem_append_left _ ht)))
      (ih' (fun t ht => agree t (List.mem_append_right _ ht)))
  | altLeft _ ih => exact .altLeft (ih agree)
  | altRight _ ih => exact .altRight (ih agree)
  | optionalEmpty => exact .optionalEmpty
  | optionalSome _ ih => exact .optionalSome (ih agree)
  | manyEmpty => exact .manyEmpty
  | manyCons _ _ same ih ih' =>
    exact .manyCons (ih (fun t ht => agree t (List.mem_append_left _ ht)))
      (ih' (fun t ht => agree t (List.mem_append_right _ ht))) same

theorem Valid.derives (h : Valid source symbol v) :
    EBNF.Derives source v.expr (v.tokens.map symbol) := by
  induction h with
  | empty => exact .empty
  | terminal same nonempty => simpa [Value.expr, Value.tokens, same] using
      (EBNF.Derives.terminal (grammar := source) nonempty)
  | named rule _ ih => exact .ref rule ih
  | seq _ _ ih ih' => simpa [Value.expr, Value.tokens, List.map_append] using
      EBNF.Derives.seq ih ih'
  | altLeft _ ih => exact .altLeft ih
  | altRight _ ih => exact .altRight ih
  | optionalEmpty => exact .optionalEmpty
  | optionalSome _ ih => exact .optionalSome ih
  | manyEmpty => exact .manyEmpty
  | manyCons _ _ same ih ih' =>
    simpa [Value.expr, Value.tokens, List.map_append] using
      EBNF.Derives.manyCons ih (same ▸ ih')

/-- Raw terminals deliberately carry no nonempty requirement. Only a used
terminal fragment discharges that obligation through `Interprets`. -/
def Good (source : EBNF.Grammar) (p : Prepared) (encode : α → Nat)
    (meanings : Meanings) (c : Cell α) : Prop :=
  Fits p meanings c ∧ match c.1 with
  | .terminal t => ∃ a, encode a = t ∧ c.2 = .terminal (p.decode t) a
  | .nonterminal _ => Valid source (p.decode ∘ encode) c.2

theorem Reads.valid (h : Reads f cs v rest) (interprets : f.Interprets p meanings)
    (good : ∀ c ∈ cs, Good source p encode meanings c) :
    Valid source (p.decode ∘ encode) v := by
  induction h with
  | empty => exact .empty
  | @atom f s v rest atomic rhs expr =>
    have hg := good (s, v) (by simp)
    cases f with
    | empty | seq => contradiction
    | terminal symbol code =>
      simp only [Fragment.rhs, List.singleton_inj] at rhs
      subst s
      obtain ⟨a, ha, rfl⟩ := hg.2
      have hd : p.decode code = symbol := by simp [Prepared.decode, interprets.1]
      exact .terminal (by simp [ha]) (hd ▸ interprets.2.2)
    | ref | alt | optional | many =>
      simp only [Fragment.rhs, List.singleton_inj] at rhs
      subst s
      exact hg.2
  | seq left right ih ih' =>
    apply Valid.seq (ih interprets.1 good)
    apply ih' interprets.2
    obtain ⟨_, front, hcs, _, _⟩ := left.exact
    intro c hc
    exact good c (hcs ▸ List.mem_append_right front hc)

theorem Applies.valid (h : Applies r cs v) (valid : r.Valid source p meanings)
    (good : ∀ c ∈ cs, Good source p encode meanings c) :
    Valid source (p.decode ∘ encode) v := by
  cases h with
  | named hr =>
    apply Valid.named
    · simpa only [hr.exact.1] using valid.2.1
    · exact hr.valid valid.2.2 good
  | altLeft hr => exact .altLeft (hr.valid valid.2 good)
  | altRight hr => exact .altRight (hr.valid valid.2 good)
  | optionalEmpty => exact .optionalEmpty
  | optionalSome hr => exact .optionalSome (hr.valid valid.2 good)
  | manyEmpty => exact .manyEmpty
  | manyCons hr he =>
    obtain ⟨_, front, hcs, _, _⟩ := hr.exact
    have ht := good _ (hcs ▸ List.mem_append_right front (List.mem_singleton_self _))
    exact .manyCons (hr.valid valid.2 good) ht.2 (by rw [he, hr.exact.1])

mutual
  /-- Executable entry: no prepared grammar or lowering witness is evaluated.
  Child conversion is structural recursion on the finite payload CST. -/
  def convert (decode : Nat → Parser.Symbol) (encode : α → Nat)
      (rules : Array AnnotatedRule) (tree : PayloadTree α) : Option (Cell α) :=
    match tree with
    | .terminal a => some (.terminal (encode a), .terminal (decode (encode a)) a)
    | .node index n cs => do
      let rule ← rules[index]?
      if rule.production.input ≠ n then none else do
        let children ← convertForest decode encode rules cs
        if children.map Prod.fst ≠ rule.production.output then none else do
          let value ← applyRule rule children
          return (.nonterminal n, value)
    termination_by sizeOf tree

  def convertForest (decode : Nat → Parser.Symbol) (encode : α → Nat)
      (rules : Array AnnotatedRule) (trees : List (PayloadTree α)) : Option (List (Cell α)) :=
    match trees with
    | [] => some []
    | c :: cs => do
      let child ← convert decode encode rules c
      let children ← convertForest decode encode rules cs
      return child :: children
    termination_by sizeOf trees
end

mutual
  /-- Actual production index, nonterminal, child forest and chosen annotation
  all occur in this relation. Word equality cannot establish it. -/
  inductive Converts (decode : Nat → Parser.Symbol) (encode : α → Nat)
      (rules : Array AnnotatedRule) : PayloadTree α → Cell α → Prop where
    | terminal : Converts decode encode rules (.terminal a)
        (.terminal (encode a), .terminal (decode (encode a)) a)
    | node (lookup : rules[index]? = some r) (lhs : r.production.input = n)
        (children : ForestConverts decode encode rules cs values)
        (symbols : values.map Prod.fst = r.production.output)
        (action : Applies r values v) :
        Converts decode encode rules (.node index n cs) (.nonterminal n, v)

  inductive ForestConverts (decode : Nat → Parser.Symbol) (encode : α → Nat)
      (rules : Array AnnotatedRule) : List (PayloadTree α) → List (Cell α) → Prop where
    | nil : ForestConverts decode encode rules [] []
    | cons (head : Converts decode encode rules c v)
        (tail : ForestConverts decode encode rules cs vs) :
        ForestConverts decode encode rules (c :: cs) (v :: vs)
end

theorem convert_iff (decode : Nat → Parser.Symbol) (encode : α → Nat)
    (rules : Array AnnotatedRule) (tree : PayloadTree α) : ∀ c,
    convert decode encode rules tree = some c ↔ Converts decode encode rules tree c := by
  refine PayloadTree.rec
    (motive_1 := fun t => ∀ c, convert decode encode rules t = some c ↔
      Converts decode encode rules t c)
    (motive_2 := fun ts => ∀ cs, convertForest decode encode rules ts = some cs ↔
      ForestConverts decode encode rules ts cs) ?_ ?_ ?_ ?_ tree
  · intro a c
    constructor
    · intro h; simp only [convert, Option.some.injEq] at h; subst c; exact .terminal
    · intro h; cases h; simp [convert]
  · intro index n cs ih c
    constructor
    · intro h
      cases hr : rules[index]? with
      | none => simp [convert, hr] at h
      | some r =>
        by_cases hn : r.production.input = n
        · cases hc : convertForest decode encode rules cs with
          | none => simp [convert, hr, hc] at h
          | some values =>
            by_cases hs : values.map Prod.fst = r.production.output
            · cases ha : applyRule r values with
              | none => simp [convert, hr, hn, hc, hs, ha] at h
              | some v =>
                simp [convert, hr, hn, hc, hs, ha] at h
                subst c
                exact .node hr hn ((ih _).mp hc) hs (applyRule_iff.mp ha)
            · simp [convert, hr, hn, hc, hs] at h
        · simp [convert, hr, hn] at h
    · intro h
      cases h with
      | node hr hn hc hs ha =>
        simp [convert, hr, hn, (ih _).mpr hc, hs, applyRule_iff.mpr ha]
  · intro cs
    constructor
    · intro h; simp only [convertForest, Option.some.injEq] at h; subst cs; exact .nil
    · intro h; cases h; simp [convertForest]
  · intro c cs ih it values
    constructor
    · intro h
      cases hc : convert decode encode rules c with
      | none => simp [convertForest, hc] at h
      | some v =>
        cases ht : convertForest decode encode rules cs with
        | none => simp [convertForest, hc, ht] at h
        | some vs =>
          simp [convertForest, hc, ht] at h
          subst values
          exact .cons ((ih _).mp hc) ((it _).mp ht)
    · intro h
      cases h with
      | cons hc ht => simp [convertForest, (ih _).mpr hc, (it _).mpr ht]

/-- Exact original payload recovery, without injectivity of the encoder. -/
theorem Converts.exact (h : Converts decode encode rules tree c) :
    c.1 = (tree.erase encode).symbol ∧
      c.2.tokens = tree.prependTokens [] := by
  refine Converts.rec
    (motive_1 := fun tree c _ => c.1 = (tree.erase encode).symbol ∧
      c.2.tokens = tree.prependTokens [])
    (motive_2 := fun ts cs _ => cs.map Prod.fst = (ts.map (PayloadTree.erase encode)).map Tree.symbol ∧
      leaves cs = ts.foldr PayloadTree.prependTokens []) ?_ ?_ ?_ ?_ h
  · simp [PayloadTree.erase, Tree.symbol, Value.tokens, PayloadTree.prependTokens]
  · intro index r n cs values v _ _ _ _ action ih
    exact ⟨by simp [PayloadTree.erase, Tree.symbol],
      by simpa only [PayloadTree.prependTokens] using action.exact.2.trans ih.2⟩
  · exact ⟨rfl, rfl⟩
  · intro c v cs vs _ _ ih it
    exact ⟨by simp [ih.1, it.1], by
      simp only [leaves, List.flatMap_cons, List.foldr_cons] at *
      rw [ih.2, it.2, ← PayloadTree.prependTokens_append]
      rfl⟩

theorem Converts.good {w : Witness} (h : Converts p.decode encode rules tree c)
    (exactRules : rules = w.rules) (checked : w.Conditions source p) :
    Good source p encode w.meanings c := by
  subst rules
  refine Converts.rec
    (motive_1 := fun _ c _ => Good source p encode w.meanings c)
    (motive_2 := fun _ cs _ => ∀ c ∈ cs, Good source p encode w.meanings c)
    ?_ ?_ ?_ ?_ h
  · exact ⟨rfl, _, rfl, rfl⟩
  · intro index r n cs values v lookup lhs _ _ action ih
    have valid := checked.2.2.2.2.2.2.1 r (Array.mem_of_getElem? lookup)
    exact ⟨by simpa only [Fits, ← lhs, action.exact.1] using valid.1,
      action.valid valid ih⟩
  · simp
  · intro c v cs vs _ _ ih it x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ih
    · exact it x hx

/-- No alphabet-wide nonempty assumption is needed: terminals are staged raw
until the actual annotated production uses them. -/
theorem convert_total {w : Witness} (p : Prepared) (encode : α → Nat) (rules : Array AnnotatedRule)
    (exactRules : rules = w.rules) (checked : w.Conditions source p)
    (tree : PayloadTree α) (valid : (tree.erase encode).valid p.grammar = true) :
    ∃ c, convert p.decode encode rules tree = some c := by
  subst rules
  have productions := checked.2.2.2.2.2.2.2
  refine PayloadTree.rec
    (motive_1 := fun t => (t.erase encode).valid p.grammar = true →
      ∃ c, convert p.decode encode w.rules t = some c)
    (motive_2 := fun ts => (∀ t ∈ ts, (t.erase encode).valid p.grammar = true) →
      ∃ cs, convertForest p.decode encode w.rules ts = some cs ∧
        cs.map Prod.fst = (ts.map (PayloadTree.erase encode)).map Tree.symbol ∧
        (∀ c ∈ cs, Good source p encode w.meanings c)) ?_ ?_ ?_ ?_ tree valid
  · intro a _
    exact ⟨(.terminal (encode a), .terminal (p.decode (encode a)) a), by simp [convert]⟩
  · intro index n cs ih hv
    simp only [PayloadTree.erase, Tree.valid, productions, Array.getElem?_map] at hv
    cases hr : w.rules[index]? with
    | none => simp [hr] at hv
    | some r =>
      simp only [hr, Option.map_some, Bool.and_eq_true, decide_eq_true_eq] at hv
      obtain ⟨⟨hn, hs⟩, hc⟩ := hv
      have childrenValid : ∀ t ∈ cs, (t.erase encode).valid p.grammar = true := by
        simpa using (List.all_eq_true.mp hc)
      obtain ⟨values, run, symbols, good⟩ := ih childrenValid
      have rv := checked.2.2.2.2.2.2.1 r (Array.mem_of_getElem? hr)
      have shape : values.map Prod.fst = r.production.output := symbols.trans hs.symm
      obtain ⟨v, action⟩ := applyRule_total r rv values shape (fun c hc => (good c hc).1)
      exact ⟨(.nonterminal n, v), by simp [convert, hr, hn, run, shape, action]⟩
  · intro _; exact ⟨[], by simp [convertForest], rfl, by simp⟩
  · intro c cs ih it hv
    obtain ⟨v, run⟩ := ih (hv c (by simp))
    obtain ⟨vs, runs, hs, hg⟩ := it (fun t ht => hv t (by simp [ht]))
    have fidelity := (convert_iff p.decode encode w.rules c v).mp run
    have good := fidelity.good rfl checked
    refine ⟨v :: vs, by simp [convertForest, run, runs], ?_, ?_⟩
    · simp [fidelity.exact.1, hs]
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact good
      · exact hg x hx

/-- Public CST/payload bridge. All executable dependencies are explicit runtime
data; neither a generated `Prepared` nor a witness is evaluated. -/
def build (decode : Nat → Parser.Symbol) (encode : α → Nat)
    (runtimeRules : Array AnnotatedRule) (tree : Tree) (tokens : List α) : Option (Value α) := do
  let payload ← PayloadTree.attach encode tree tokens
  let value ← convert decode encode runtimeRules payload
  return value.2

/-- The public result retains the actual payload CST and annotation fidelity,
and records the named source start expression as well as independent semantics. -/
def Root (source : EBNF.Grammar) (start : Nat) (decode : Nat → Parser.Symbol)
    (encode : α → Nat) (rules : Array AnnotatedRule) (tree : Tree)
    (tokens : List α) (v : Value α) : Prop :=
  v.prependTokens [] = tokens ∧
  (∃ payload, PayloadTree.attach encode tree tokens = some payload ∧
    payload.erase encode = tree ∧ Converts decode encode rules payload (.nonterminal start, v)) ∧
  ∃ name body tail, source = (name, body) :: tail ∧ v.expr = .ref name ∧
    Valid source (decode ∘ encode) v ∧
    EBNF.Derives source (.ref name) (tokens.map (decode ∘ encode)) ∧
    EBNF.Accepts source (tokens.map (decode ∘ encode))

/-- Totality reaches the public executable on every checked tree and aligned
payload list. Decoder and rule projection agreements are proof-only premises. -/
theorem build_total {w : Witness} (p : Prepared) (decode : Nat → Parser.Symbol)
    (encode : α → Nat) (rules : Array AnnotatedRule)
    (decoder : decode = p.decode) (exactRules : rules = w.rules)
    (checked : w.Conditions source p)
    (checkedTree : checkTree p.grammar (tokens.map encode) tree = true) :
    ∃ v, build decode encode rules tree tokens = some v ∧
      Root source p.grammar.start decode encode rules tree tokens v := by
  subst decode
  obtain ⟨word, start, _⟩ := checkTree_sound _ _ _ checkedTree
  obtain ⟨payload, attached⟩ := (PayloadTree.attach_iff encode tree tokens).mpr word
  obtain ⟨erased, leaves⟩ := PayloadTree.attach_sound encode tree tokens attached
  have treeValid : tree.valid p.grammar = true := by
    simp only [checkTree, Bool.and_eq_true, decide_eq_true_eq] at checkedTree
    exact checkedTree.1.1
  obtain ⟨⟨atom, v⟩, converted⟩ := convert_total p encode rules exactRules checked payload
    (by simpa only [erased] using treeValid)
  have fidelity := (convert_iff p.decode encode rules payload (atom, v)).mp converted
  have atomStart : atom = .nonterminal p.grammar.start := by
    have hs := fidelity.exact.1
    rw [erased] at hs
    exact hs.trans start
  subst atom
  have good := fidelity.good exactRules checked
  have recovered : v.prependTokens [] = tokens := by
    simpa only [Value.prependTokens_eq, List.append_nil] using fidelity.exact.2.trans leaves
  have semantic : Valid source (p.decode ∘ encode) v := good.2
  have derivation : EBNF.Derives source v.expr (tokens.map (p.decode ∘ encode)) := by
    have yieldEq : v.tokens = tokens := by
      simpa only [Value.prependTokens_eq, List.append_nil] using recovered
    simpa only [yieldEq] using semantic.derives
  have nonempty := checked.1
  cases source with
  | nil => exact False.elim (nonempty rfl)
  | cons rule tail =>
    obtain ⟨name, body⟩ := rule
    have initial := (checked.2.2.2.2.2.1 ⟨0, by simp⟩).1
    have lookup := good.1
    change w.meanings[p.grammar.start]? = some v.expr at lookup
    rw [checked.2.1, initial] at lookup
    have expression : v.expr = .ref name := (Option.some.inj lookup).symm
    have derives : EBNF.Derives ((name, body) :: tail) (.ref name)
        (tokens.map (p.decode ∘ encode)) := expression ▸ derivation
    refine ⟨v, by simp [build, attached, converted], recovered,
      ⟨payload, attached, erased, fidelity⟩, name, body, tail, rfl, expression,
      semantic, derives, ?_⟩
    exact ⟨name, body, tail, rfl, derives⟩

/-- Composition with the actual token parser; parser errors yield no value. -/
def parse (parser : TokenParser α) (decode : Nat → Parser.Symbol)
    (rules : Array AnnotatedRule) (tokens : List α) : Option (Value α) :=
  match parser.run tokens with
  | .ok tree => build decode parser.encode rules tree tokens
  | .error _ => none

theorem parse_total {w : Witness} (parser : TokenParser α) (p : Prepared)
    (decode : Nat → Parser.Symbol) (rules : Array AnnotatedRule)
    (grammar : parser.grammar = p.grammar) (decoder : decode = p.decode)
    (exactRules : rules = w.rules) (checked : w.Conditions source p)
    (parsed : parser.run tokens = .ok tree) :
    ∃ v, parse parser decode rules tokens = some v ∧
      Root source p.grammar.start decode parser.encode rules tree tokens v := by
  have checkedTree := parser.checked tokens tree parsed
  rw [grammar] at checkedTree
  obtain ⟨v, built, root⟩ := build_total p decode parser.encode rules decoder exactRules checked checkedTree
  exact ⟨v, by simpa only [parse, parsed] using built, root⟩

/-- Every public success carries the actual parser execution, named start
realization, exact payloads and independent EBNF derivation. -/
theorem parse_sound {w : Witness} (parser : TokenParser α) (p : Prepared)
    (decode : Nat → Parser.Symbol) (rules : Array AnnotatedRule)
    (grammar : parser.grammar = p.grammar) (decoder : decode = p.decode)
    (exactRules : rules = w.rules) (checked : w.Conditions source p)
    (success : parse parser decode rules tokens = some v) :
    ∃ tree, parser.run tokens = .ok tree ∧
      Root source p.grammar.start decode parser.encode rules tree tokens v := by
  cases parsed : parser.run tokens with
  | error failure => simp [parse, parsed] at success
  | ok tree =>
    obtain ⟨value, run, root⟩ :=
      parse_total parser p decode rules grammar decoder exactRules checked parsed
    have same : value = v := Option.some.inj (run.symm.trans success)
    subst value
    exact ⟨tree, rfl, root⟩

/-- Structural conversion preserves the actual token parser's whole language;
its action checks cannot introduce a new syntax-completeness restriction. -/
theorem parse_accepts_iff {w : Witness} (parser : TokenParser α) (p : Prepared)
    (decode : Nat → Parser.Symbol) (rules : Array AnnotatedRule)
    (grammar : parser.grammar = p.grammar) (decoder : decode = p.decode)
    (exactRules : rules = w.rules) (checked : w.Conditions source p) :
    (∃ v, parse parser decode rules tokens = some v) ↔
      parser.grammar.Accepts (tokens.map parser.encode) := by
  constructor
  · rintro ⟨v, success⟩
    obtain ⟨tree, parsed, _⟩ :=
      parse_sound parser p decode rules grammar decoder exactRules checked success
    exact (parser.accepts_iff tokens).mpr ⟨tree, parsed⟩
  · intro accepted
    obtain ⟨tree, parsed⟩ := (parser.accepts_iff tokens).mp accepted
    obtain ⟨v, success, _⟩ :=
      parse_total parser p decode rules grammar decoder exactRules checked parsed
    exact ⟨v, success⟩

end Parser.LALR.Frontend.Structure
