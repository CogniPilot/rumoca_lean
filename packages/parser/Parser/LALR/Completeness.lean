import Parser.LALR.ItemCheck
import Parser.LALR.Execution
import Parser.LALR.DerivationTrees

/-! Derivation-directed execution of the actual LR interpreter. The grammar,
tables and item annotations are arbitrary. The item validator supplies the
shift/goto/reduction/closure obligations; no generator behavior is assumed. -/
namespace Parser.LALR

/-- One shift per terminal and one reduction per production node. -/
def Tree.steps : Tree → Nat
  | .terminal _ => 1
  | .node _ _ children => (children.map Tree.steps).sum + 1
  termination_by tree => sizeOf tree

namespace Completeness

variable {g : Grammar} {tables : Tables} {facts : Array First} {states : Array ItemSet}

theorem forest_derives {trees : List Tree} (valid : ∀ tree ∈ trees, tree.valid g = true) :
    g.semantics.Derives (trees.map Tree.symbol)
      ((trees.flatMap Tree.word).map _root_.Symbol.terminal) := by
  induction trees with
  | nil => exact .refl _
  | cons tree rest ih =>
    have ht := Tree.valid_derives g tree (valid tree (by simp))
    have hr := ih (fun t h => valid t (by simp [h]))
    simpa only [List.map_cons, List.flatMap_cons, List.map_append, List.singleton_append] using
      (ht.append_right (rest.map Tree.symbol)).trans
        (hr.append_left (tree.word.map _root_.Symbol.terminal))

theorem word_valid (tree : Tree) : tree.valid g = true →
    ∀ token ∈ tree.word, token < g.terminals := by
  refine Tree.rec (motive_1 := fun tree => tree.valid g = true →
    ∀ token ∈ tree.word, token < g.terminals)
    (motive_2 := fun trees => (∀ tree ∈ trees, tree.valid g = true) →
    ∀ token ∈ trees.flatMap Tree.word, token < g.terminals) ?_ ?_ ?_ ?_ tree
  · intro token hv t ht
    simp only [Tree.word] at ht
    obtain rfl := List.mem_singleton.mp ht
    simpa only [Tree.valid, decide_eq_true_eq] using hv
  · intro index n children ih hv
    unfold Tree.valid at hv
    split at hv
    · contradiction
    · simp only [Bool.and_eq_true] at hv
      simp only [Tree.word]
      apply ih
      simpa using List.all_eq_true.mp hv.2
  · intro _ token ht
    contradiction
  · intro tree rest it ir valid token ht
    simp only [List.flatMap_cons, List.mem_append] at ht
    rcases ht with ht | hr
    · exact it (valid tree (by simp)) token ht
    · exact ir (fun t h => valid t (by simp [h])) token hr

def Ready (tables : Tables) (states : Array ItemSet)
    (stack : List Frame) (following : Nat) (tree : Tree) (target : Nat) : Prop :=
  target < states.size ∧ match tree with
  | .terminal token => tables.action (Configuration.state ⟨stack, []⟩) token = some (.shift target)
  | .node index n _ => tables.goto (Configuration.state ⟨stack, []⟩) n = some target ∧
      (⟨index, 0, following⟩ : Item) ∈ ItemCheck.items states (Configuration.state ⟨stack, []⟩)

def TreeRuns (g : Grammar) (tables : Tables) (states : Array ItemSet) (tree : Tree) : Prop :=
  ∀ (stack : List Frame) (tail : List Nat) (target : Nat),
    tree.valid g = true → (∀ token ∈ tail, token < g.terminals) →
    Ready tables states stack (tail.headD g.terminals) tree target →
    Execution.Steps g tables tree.steps ⟨stack, tree.word ++ tail⟩
      ⟨⟨target, tree⟩ :: stack, tail⟩

def ForestRuns (g : Grammar) (tables : Tables) (states : Array ItemSet)
    (children : List Tree) : Prop :=
  ∀ (stack : List Frame) (tail : List Nat) (item : Item) (p : Production),
    (∀ tree ∈ children, tree.valid g = true) → (∀ token ∈ tail, token < g.terminals) →
    (augment g).productions[item.production]? = some p →
    p.output.drop item.dot = children.map Tree.symbol →
    item.lookahead = tail.headD g.terminals →
    item ∈ ItemCheck.items states (Configuration.state ⟨stack, []⟩) →
    ∃ frames : List Frame, frames.reverse.map Frame.tree = children ∧
      Execution.Steps g tables (children.map Tree.steps).sum
        ⟨stack, children.flatMap Tree.word ++ tail⟩ ⟨frames ++ stack, tail⟩ ∧
      { item with dot := item.dot + children.length } ∈
        ItemCheck.items states (Configuration.state ⟨frames ++ stack, []⟩)

theorem tree_runs (checked : ItemCheck.validate g tables facts states = true) (tree : Tree) :
    TreeRuns g tables states tree := by
  have sizes := (ItemCheck.validate_iff.mp checked).2.1
  refine Tree.rec (motive_1 := TreeRuns g tables states)
    (motive_2 := ForestRuns g tables states) ?_ ?_ ?_ ?_ tree
  · intro token stack tail target valid _ ready
    simp only [Tree.valid, decide_eq_true_eq] at valid
    have targetBound := ready.1
    have hs := Execution.shift stack token tail target valid
      (by omega) ready.2
    simpa only [Tree.steps, Tree.word, List.singleton_append] using
      (Execution.Steps.next hs (.refl _) : Execution.Steps g tables 1 _ _)
  · intro index n children ih stack tail target valid tailValid ready
    obtain ⟨targetBound, goto, member⟩ := ready
    unfold Tree.valid at valid
    split at valid
    · contradiction
    · rename_i p rule
      simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
      obtain ⟨⟨lhs, rhs⟩, childValid⟩ := valid
      have childValid : ∀ child ∈ children, child.valid g = true := by
        simpa using List.all_eq_true.mp childValid
      have bound := (Array.getElem?_eq_some_iff.mp rule).1
      have augmented : (augment g).productions[index]? = some p := by
        change (g.productions.push ⟨g.nonterminals, [.nonterminal g.start]⟩)[index]? = some p
        rw [Array.getElem?_push_lt bound]
        exact congrArg some (Array.getElem?_eq_some_iff.mp rule).2
      obtain ⟨frames, childrenEq, execution, finalItem⟩ :=
        ih stack tail ⟨index, 0, tail.headD g.terminals⟩ p childValid tailValid
          augmented (by simpa using rhs) rfl member
      have complete := (ItemCheck.entry_at checked finalItem).2.2
      have count : frames.length = p.output.length := by
        have hf := congrArg List.length childrenEq
        have hp := congrArg List.length rhs
        simp only [List.length_map, List.length_reverse] at hf hp
        omega
      have action : tables.action (Configuration.state ⟨frames ++ stack, tail⟩)
          (tail.headD g.terminals) = some (.reduce index) := by
        have neq : index ≠ g.productions.size := by omega
        have endRule : p.output[children.length]? = none := by rw [rhs]; simp
        simpa [ItemCheck.Advances, nextSymbol, augmented, endRule, neq] using complete
      have inputValid : tail = [] ∨ tail.headD g.terminals < g.terminals := by
        cases tail with
        | nil => exact Or.inl rfl
        | cons token rest => exact Or.inr (tailValid token (by simp))
      have reduce := Execution.reduce frames stack tail index target p inputValid rule count
        (rhs.trans (congrArg (List.map Tree.symbol) childrenEq).symm) action
        (by simpa only [lhs] using goto) (by omega)
      have last : Execution.Steps g tables 1 ⟨frames ++ stack, tail⟩
          ⟨⟨target, .node index n children⟩ :: stack, tail⟩ := by
        rw [childrenEq, lhs] at reduce
        exact .next reduce (.refl _)
      simpa only [Tree.steps, Tree.word] using execution.trans last
  · intro stack tail item p _ _ _ _ _ member
    refine ⟨[], rfl, .refl _, ?_⟩
    simpa using member
  · intro head rest headRuns restRuns stack tail item p valid tailValid rule rhs following member
    have headValid := valid head (by simp)
    have restValid : ∀ tree ∈ rest, tree.valid g = true := fun tree ht => valid tree (by simp [ht])
    have next : p.output[item.dot]? = some head.symbol := by
      have h := congrArg List.head? rhs
      simpa only [List.head?_drop, List.map_cons, List.head?_cons] using h
    have suffix : p.output.drop (item.dot + 1) = rest.map Tree.symbol := by
      rw [List.drop_add_one_eq_tail_drop, rhs]
      rfl
    have followingEq : (rest.flatMap Tree.word ++ tail).headD g.terminals =
        (rest.flatMap Tree.word).headD item.lookahead := by
      rw [following]
      cases rest.flatMap Tree.word <;> rfl
    have restTailValid : ∀ token ∈ rest.flatMap Tree.word ++ tail, token < g.terminals := by
      intro token ht
      rcases List.mem_append.mp ht with hr | ht
      · obtain ⟨child, hc, ht⟩ := List.mem_flatMap.mp hr
        exact word_valid child (restValid child hc) token ht
      · exact tailValid token ht
    have advance := (ItemCheck.entry_at checked member).2.2
    have prepared : ∃ target, Ready tables states stack
        ((rest.flatMap Tree.word ++ tail).headD g.terminals) head target ∧
        { item with dot := item.dot + 1 } ∈ ItemCheck.items states target := by
      cases head with
      | terminal token =>
        simp only [ItemCheck.Advances, nextSymbol, rule, bind, Option.bind_some, next, Tree.symbol] at advance
        obtain ⟨target, action, advanced⟩ := advance
        exact ⟨target.val, ⟨target.isLt, action⟩, advanced⟩
      | node index n children =>
        simp only [ItemCheck.Advances, nextSymbol, rule, bind, Option.bind_some, next, Tree.symbol] at advance
        obtain ⟨target, goto, advanced⟩ := advance
        unfold Tree.valid at headValid
        split at headValid
        · contradiction
        · rename_i childRule childLookup
          simp only [Bool.and_eq_true, decide_eq_true_eq] at headValid
          obtain ⟨indexBound, childEq⟩ := Array.getElem?_eq_some_iff.mp childLookup
          have closed := (ItemCheck.entry_at checked member).2.1
          simp only [ItemCheck.Closed, rule, next, Tree.symbol] at closed
          have derives : g.semantics.Derives (p.output.drop (item.dot + 1))
              ((rest.flatMap Tree.word).map _root_.Symbol.terminal) := by
            exact (congrArg (fun (symbols : List Atom) => g.semantics.Derives symbols
              ((rest.flatMap Tree.word).map _root_.Symbol.terminal)) suffix).mpr
                (forest_derives restValid)
          have lookahead := FirstProofs.lookahead_complete
            (ItemCheck.validate_iff.mp checked).2.2.1 derives (following := item.lookahead)
          have childLhs : g.productions[index].input = n := by rw [childEq]; exact headValid.1.1
          have initial := closed ⟨index, indexBound⟩ childLhs _ lookahead
          refine ⟨target.val, ⟨target.isLt, goto, ?_⟩, advanced⟩
          simpa only [followingEq] using initial
    obtain ⟨target, ready, advanced⟩ := prepared
    have headExecution := headRuns stack (rest.flatMap Tree.word ++ tail) target
      headValid restTailValid ready
    have advancedAt : { item with dot := item.dot + 1 } ∈ ItemCheck.items states
        (Configuration.state ⟨⟨target, head⟩ :: stack, []⟩) := advanced
    obtain ⟨frames, framesEq, restExecution, finalItem⟩ := restRuns
      (⟨target, head⟩ :: stack) tail { item with dot := item.dot + 1 } p
      restValid tailValid rule suffix following advancedAt
    refine ⟨frames ++ [⟨target, head⟩], ?_, ?_, ?_⟩
    · simp only [List.reverse_append, List.reverse_singleton,
        List.map_cons, List.singleton_append, framesEq]
    · simpa only [List.map_cons, List.sum_cons, List.flatMap_cons, List.append_assoc,
        List.singleton_append] using headExecution.trans restExecution
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
        List.append_assoc, List.singleton_append] using finalItem

/-- The actual public parser accepts every valid start tree using precisely
one shift/reduction per tree constructor, followed by EOF acceptance. -/
theorem parse_tree (checked : ItemCheck.validate g tables facts states = true)
    (tree : Tree) (valid : tree.valid g = true)
    (start : tree.symbol = .nonterminal g.start) :
    parse g tables (tree.steps + 1) tree.word = .ok tree := by
  have initial := ItemCheck.initial checked
  have entry := ItemCheck.entry_at checked initial
  have augmented : (augment g).productions[g.productions.size]? =
      some ⟨g.nonterminals, [.nonterminal g.start]⟩ := by simp [augment]
  have advance := entry.2.2
  simp only [ItemCheck.Advances, nextSymbol, augmented, bind, Option.bind_some,
    List.getElem?_cons_zero] at advance
  obtain ⟨target, goto, finalItem⟩ := advance
  have acceptItem := (ItemCheck.entry_at checked finalItem).2.2
  have accepting : tables.action target.val g.terminals = some .accept := by
    simpa [ItemCheck.Advances, nextSymbol, augmented] using acceptItem
  have runs : Execution.Steps g tables tree.steps ⟨[], tree.word⟩
      ⟨[⟨target.val, tree⟩], []⟩ := by
    have ready : Ready tables states [] g.terminals tree target.val := by
      cases tree with
      | terminal token => simp [Tree.symbol] at start
      | node index n children =>
        have same : n = g.start := Symbol.nonterminal.inj start
        have hv := valid
        unfold Tree.valid at hv
        split at hv
        · contradiction
        · rename_i p rule
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
          obtain ⟨bound, prod⟩ := Array.getElem?_eq_some_iff.mp rule
          have lhs : g.productions[index].input = g.start := by rw [prod, hv.1.1, same]
          have closure := entry.2.1
          simp only [ItemCheck.Closed, augmented, List.getElem?_cons_zero] at closure
          have lookahead : g.terminals ∈ lookaheads facts [] g.terminals := by
            exact FirstProofs.lookahead_complete
              (ItemCheck.validate_iff.mp checked).2.2.1
              (word := []) (ContextFreeGrammar.Derives.refl [])
          have member := closure ⟨index, bound⟩ lhs g.terminals (by simpa using lookahead)
          exact ⟨target.isLt, by simpa [Configuration.state, same] using goto, member⟩
    simpa only [List.append_nil, List.headD_nil] using
      tree_runs checked tree [] [] target.val valid (by simp) ready
  have accepted := Execution.accept tree target.val start accepting
  have run : LALR.run g tables (tree.steps + 1) ⟨[], tree.word⟩ = .ok tree := by
    rw [runs.run 1, LALR.run, accepted]
  have certificate : checkTree g tree.word tree = true := by
    simp [checkTree, valid, start, Tree.prependWord_eq]
  unfold parse
  rw [run]
  change (if checkTree g tree.word tree then Except.ok tree
    else Except.error Failure.invalidTree) = Except.ok tree
  rw [certificate]
  rfl

/-- Completeness is stated in mathlib's independent CFG language semantics;
callers do not have to supply trees or trust the table generator. The separate
resource certificate must turn this finite existence into an input-size bound. -/
theorem parse_complete (checked : ItemCheck.validate g tables facts states = true)
    (accepted : g.Accepts word) :
    ∃ fuel tree, parse g tables fuel word = .ok tree := by
  obtain ⟨tree, valid, start, yield⟩ :=
    g.accepts_tree (ItemCheck.validate_iff.mp checked).1 accepted
  exact ⟨tree.steps + 1, tree, yield ▸ parse_tree checked tree valid start⟩

theorem accepts_iff_parse (checked : ItemCheck.validate g tables facts states = true) :
    g.Accepts word ↔ ∃ fuel tree, parse g tables fuel word = .ok tree := by
  constructor
  · exact parse_complete checked
  · rintro ⟨fuel, tree, parsed⟩
    exact (parse_sound g tables fuel word tree parsed).2.2

end Completeness
end Parser.LALR
