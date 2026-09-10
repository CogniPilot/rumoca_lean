import Parser.LALR.Soundness
import Parser.Source

/-! Automatic spans for every production of any generated grammar. Grammar
leaves and production identities are unchanged. Empty productions are anchored
at the next token's start, or EOF; parent ranges cover all children, including
empty ones. This may include inter-token trivia at a nullable boundary. -/
namespace Parser.LALR
open Source

inductive LocatedTree (source : String) where
  | terminal (token : Located source Nat)
  | node (production nonterminal : Nat) (span : Span source) (children : List (LocatedTree source))

namespace LocatedTree
variable {source : String}

def span : LocatedTree source → Span source
  | .terminal t => t.span
  | .node _ _ range _ => range

def erase : LocatedTree source → Tree
  | .terminal t => .terminal t.value
  | .node p n _ cs => .node p n (cs.map erase)
  termination_by t => sizeOf t

/-- Accumulator yield, linear in tree size. -/
def prependTokens : LocatedTree source → List (Located source Nat) → List (Located source Nat)
  | .terminal t, rest => t :: rest
  | .node _ _ _ cs, rest => cs.foldr prependTokens rest
  termination_by t _ => sizeOf t

def cover (anchor : source.Pos) (cs : List (LocatedTree source)) : Span source :=
  cs.foldr (fun child tail => child.span.cover tail) (.point anchor)

theorem cover_children (anchor : source.Pos) (cs : List (LocatedTree source)) :
    ∀ c ∈ cs, (cover anchor cs).Contains c.span := by
  induction cs with
  | nil => simp
  | cons a cs ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Span.cover_left _ _
    · have h := ih c hc
      have hh := Span.cover_right a.span (cover anchor cs)
      exact ⟨Nat.le_trans hh.1 h.1, Nat.le_trans h.2 hh.2⟩

def nodeWithSpan (p n : Nat) (anchor : source.Pos) (cs : List (LocatedTree source)) :
    LocatedTree source := .node p n (cover anchor cs) cs

@[simp] theorem erase_nodeWithSpan (p n : Nat) (anchor : source.Pos) (cs : List (LocatedTree source)) :
    (nodeWithSpan p n anchor cs).erase = .node p n (cs.map erase) := by
  simp [nodeWithSpan, erase]

theorem node_covers (p n : Nat) (anchor : source.Pos) (cs : List (LocatedTree source)) :
    ∀ c ∈ cs, (nodeWithSpan p n anchor cs).span.Contains c.span :=
  cover_children anchor cs

/-- Every descendant is covered by its direct parent. -/
inductive WellSpanned : LocatedTree source → Prop where
  | terminal : WellSpanned (.terminal t)
  | node : (∀ c ∈ cs, range.Contains c.span) →
      (∀ c ∈ cs, WellSpanned c) → WellSpanned (.node p n range cs)

theorem empty_span (p n : Nat) (anchor : source.Pos) :
    (nodeWithSpan p n anchor []).span = Span.point anchor := rfl

end LocatedTree

/- Annotation consumes token ordinals once. Fallback ranges are only candidate
values: the public API checks every terminal's value AND range against input. -/
mutual
  def decorate (input : Array (Located source Nat)) (tree : Tree) (i : Nat) :
      LocatedTree source × Nat :=
    match tree with
    | .terminal t =>
      (.terminal ⟨t, (input[i]?).map (·.span) |>.getD (.point source.endPos)⟩, i + 1)
    | .node p n cs =>
      let (children, next) := decorateForest input cs i
      let anchor := (input[i]?).map (·.span.start) |>.getD source.endPos
      (LocatedTree.nodeWithSpan p n anchor children, next)
    termination_by sizeOf tree

  def decorateForest (input : Array (Located source Nat)) (cs : List Tree) (i : Nat) :
      List (LocatedTree source) × Nat :=
    match cs with
    | [] => ([], i)
    | c :: cs =>
      let (child, next) := decorate input c i
      let (children, stop) := decorateForest input cs next
      (child :: children, stop)
    termination_by sizeOf cs
end

/-- Locations cannot change even one terminal or production in the parse. -/
theorem decorate_erases (input : Array (Located source Nat)) (tree : Tree) (i : Nat) :
    (decorate input tree i).1.erase = tree := by
  refine Tree.rec
    (motive_1 := fun tree => ∀ i, (decorate input tree i).1.erase = tree)
    (motive_2 := fun cs => ∀ i,
      (decorateForest input cs i).1.map LocatedTree.erase = cs) ?_ ?_ ?_ ?_ tree i
  · intro t i; simp [decorate, LocatedTree.erase]
  · intro p n cs ih i
    simpa [decorate, LocatedTree.nodeWithSpan, LocatedTree.erase] using congrArg (Tree.node p n) (ih i)
  · intro i; simp [decorateForest]
  · intro c cs ih ir i
    simp [decorateForest, ih, ir]

theorem decorate_wellSpanned (input : Array (Located source Nat)) (tree : Tree) (i : Nat) :
    (decorate input tree i).1.WellSpanned := by
  refine Tree.rec
    (motive_1 := fun tree => ∀ i, (decorate input tree i).1.WellSpanned)
    (motive_2 := fun cs => ∀ i, ∀ c ∈ (decorateForest input cs i).1,
      c.WellSpanned) ?_ ?_ ?_ ?_ tree i
  · intro t i; simp only [decorate]; exact .terminal
  · intro p n cs ih i
    simp only [decorate, LocatedTree.nodeWithSpan]
    exact .node (LocatedTree.cover_children _ _) (ih i)
  · intro i; simp [decorateForest]
  · intro c cs ih ir i
    simpa only [decorateForest, List.mem_cons, forall_eq_or_imp] using And.intro (ih i) (ir _)

/-- The located result binds every leaf, including its exact range, to the
input, while retaining the existing parser's complete grammar certificate. -/
structure LocatedParse (g : Grammar) (tables : Tables) (fuel : Nat)
    (input : List (Located source Nat)) where
  tree : Tree
  located : LocatedTree source
  parsed : parse g tables fuel (input.map (·.value)) = .ok tree
  erases : located.erase = tree
  terminals : located.prependTokens [] = input
  wellSpanned : located.WellSpanned

def parseLocated (g : Grammar) (tables : Tables) (fuel : Nat)
    (input : List (Located source Nat)) :
    Except Failure (LocatedParse g tables fuel input) :=
  match hp : parse g tables fuel (input.map (·.value)) with
  | .error e => .error e
  | .ok tree =>
    let located := (decorate input.toArray tree 0).1
    if ht : located.prependTokens [] = input then
      .ok ⟨tree, located, hp, decorate_erases _ _ _, ht, decorate_wellSpanned _ _ _⟩
    else .error .invalidTree

theorem LocatedParse.sound (p : LocatedParse (source := source) g tables fuel input) :
    g.Accepts (input.map (·.value)) :=
  (parse_sound _ _ _ _ _ p.parsed).2.2

end Parser.LALR
