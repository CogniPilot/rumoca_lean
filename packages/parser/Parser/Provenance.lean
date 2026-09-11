import Parser.Source

/-! Compact, checked origin graphs. Source payloads and rule identifiers are
supplied by the owning frontend/compiler. All generated nodes retain at least
one parent; appending a node cannot introduce a cycle or a dangling reference.
Runtime storage uses Lean's array implementation. -/
namespace Parser.Provenance

/-- A source occurrence with checked input identity and UTF-8 boundaries.
The input array is a type index, not a duplicated field on each occurrence. -/
structure SourceRef (inputs : Array Source.Input) where
  file : Fin inputs.size
  span : Source.Span inputs[file].source

/-- A rule-created node has a required first parent. The tail permits operations
that combine several equations, without constructing one misleading source span. -/
inductive Node (Site Rule : Type) where
  | source (site : Site)
  | derived (rule : Rule) (parent : Nat) (others : Array Nat)
  | generated (rule : Rule) (parent : Nat) (others : Array Nat)

/-- A proof-facing view of edges; ordinary graph lookup remains an array access. -/
def Node.parents : Node Site Rule → List Nat
  | .source _ => []
  | .derived _ parent others | .generated _ parent others => parent :: others.toList

structure Table (Site Rule : Type) where
  nodes : Array (Node Site Rule)
  prior : ∀ (index : Nat) (bound : index < nodes.size) (parent : Nat),
    parent ∈ nodes[index].parents → parent < index

/-- Nominal references retain their owning table in their type. -/
structure Ref (table : Table Site Rule) where
  index : Fin table.nodes.size

namespace Table

def empty : Table Site Rule := ⟨#[], by intro index bound; simp at bound⟩

def fromSources (sites : Array Site) : Table Site Rule where
  nodes := sites.map Node.source
  prior := by intro index bound parent member; simp [Node.parents] at member

def get (table : Table Site Rule) (ref : Ref table) : Node Site Rule := table.nodes[ref.index]

/-- Append with a checked backward-edge condition. Proofs erase during native
compilation; this does not revalidate or copy all earlier graph records. -/
def push (table : Table Site Rule) (node : Node Site Rule)
    (bound : ∀ parent ∈ node.parents, parent < table.nodes.size) : Table Site Rule where
  nodes := table.nodes.push node
  prior := by
    intro index hi parent member
    by_cases old : index < table.nodes.size
    · rw [Array.getElem_push_lt old] at member
      exact table.prior index old parent member
    · have last : index = table.nodes.size := by simp only [Array.size_push] at hi; omega
      subst index
      rw [Array.getElem_push_eq] at member
      exact bound parent member

/-- Existing references are stable under append. -/
def lift (table : Table Site Rule) (node : Node Site Rule) (bound) (ref : Ref table) :
    Ref (table.push node bound) :=
  ⟨⟨ref.index.val, by simpa [push] using Nat.lt_succ_of_lt ref.index.isLt⟩⟩

def last (table : Table Site Rule) (node : Node Site Rule) (bound) : Ref (table.push node bound) :=
  ⟨⟨table.nodes.size, by simp [push]⟩⟩

theorem get_lift (table : Table Site Rule) (node : Node Site Rule) (bound) (ref : Ref table) :
    (table.push node bound).get (table.lift node bound ref) = table.get ref := by
  simp [get, lift, push, Array.getElem_push_lt ref.index.isLt]

theorem get_last (table : Table Site Rule) (node : Node Site Rule) (bound) :
    (table.push node bound).get (table.last node bound) = node := by
  simp [get, last, push]

def source (table : Table Site Rule) (site : Site) : Table Site Rule :=
  table.push (.source site) (by simp [Node.parents])

private theorem parents_bound (table : Table Site Rule) (parent : Ref table)
    (others : Array (Ref table)) (p : Nat)
    (member : p ∈ parent.index.val :: (others.map (·.index.val)).toList) :
    p < table.nodes.size := by
  simp only [List.mem_cons, Array.toList_map, List.mem_map] at member
  rcases member with same | ⟨ref, _, same⟩
  · exact same ▸ parent.index.isLt
  · exact same ▸ ref.index.isLt

/-- Safe builders accept checked parent references, never raw user offsets. -/
def derive (table : Table Site Rule) (rule : Rule) (parent : Ref table)
    (others : Array (Ref table) := #[]) : Table Site Rule :=
  table.push (.derived rule parent.index.val (others.map (fun ref : Ref table => ref.index.val)))
    (parents_bound table parent others)

def generate (table : Table Site Rule) (rule : Rule) (parent : Ref table)
    (others : Array (Ref table) := #[]) : Table Site Rule :=
  table.push (.generated rule parent.index.val (others.map (fun ref : Ref table => ref.index.val)))
    (parents_bound table parent others)

/-- These references identify the newly appended records. The table is a type
index; each reference stores just its index. -/
def sourceRef (table : Table Site Rule) (site : Site) : Ref (table.source site) :=
  table.last _ _

def derivedRef (table : Table Site Rule) (rule : Rule) (parent : Ref table)
    (others : Array (Ref table) := #[]) : Ref (table.derive rule parent others) :=
  table.last _ _

def generatedRef (table : Table Site Rule) (rule : Rule) (parent : Ref table)
    (others : Array (Ref table) := #[]) : Ref (table.generate rule parent others) :=
  table.last _ _

theorem source_lookup (table : Table Site Rule) (site : Site) :
    (table.source site).get (table.sourceRef site) = .source site :=
  table.get_last _ _

theorem derived_lookup (table : Table Site Rule) (rule : Rule) (parent : Ref table)
    (others : Array (Ref table)) :
    (table.derive rule parent others).get (table.derivedRef rule parent others) =
      .derived rule parent.index.val (others.map (fun ref : Ref table => ref.index.val)) :=
  table.get_last _ _

theorem generated_lookup (table : Table Site Rule) (rule : Rule) (parent : Ref table)
    (others : Array (Ref table)) :
    (table.generate rule parent others).get (table.generatedRef rule parent others) =
      .generated rule parent.index.val (others.map (fun ref : Ref table => ref.index.val)) :=
  table.get_last _ _

end Table

/-- A proof relation for source ancestry. It neither executes a graph search nor
materializes ancestor lists in the compiled program. -/
inductive TracesTo (table : Table Site Rule) : Ref table → Site → Prop where
  | source {ref site} : table.get ref = .source site → TracesTo table ref site
  | parent {ref parent site} : parent.index.val ∈ (table.get ref).parents →
      TracesTo table parent site → TracesTo table ref site

/-- Every recorded origin reaches an actual source leaf. The backward-edge
invariant and nonempty generated-parent list rule out orphan cycles. -/
theorem traces_source (table : Table Site Rule) (ref : Ref table) :
    ∃ site, TracesTo table ref site := by
  suffices all : ∀ n (bound : n < table.nodes.size),
      ∃ site, TracesTo table ⟨⟨n, bound⟩⟩ site from all ref.index.val ref.index.isLt
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro bound
    cases node : table.nodes[n] with
    | source site => exact ⟨site, .source node⟩
    | derived rule parent others | generated rule parent others =>
      have member : parent ∈ table.nodes[n].parents := by simp [node, Node.parents]
      have prior := table.prior n bound parent member
      obtain ⟨site, trace⟩ := ih parent prior (Nat.lt_trans prior bound)
      exact ⟨site, .parent member trace⟩

/-- Appending a node preserves all source-ancestry certificates for old refs. -/
theorem TracesTo.lift {table : Table Site Rule} {ref : Ref table} {site : Site}
    (trace : TracesTo table ref site) (node : Node Site Rule) (bound) :
    TracesTo (table.push node bound) (table.lift node bound ref) site := by
  induction trace with
  | source found => exact .source ((table.get_lift node bound _).trans found)
  | @parent ref parent site member trace ih =>
      apply TracesTo.parent (parent := table.lift node bound parent) _ ih
      change parent.index.val ∈ ((table.push node bound).get (table.lift node bound ref)).parents
      rw [Table.get_lift]
      exact member

/-- A derived record retains every source ancestor of its required parent. -/
theorem TracesTo.derive {table : Table Site Rule} {parent : Ref table} {site : Site}
    (trace : TracesTo table parent site) (rule : Rule) (others : Array (Ref table) := #[]) :
    TracesTo (table.derive rule parent others) (table.derivedRef rule parent others) site := by
  apply TracesTo.parent (parent := table.lift _ _ parent) _ (trace.lift _ _)
  change parent.index.val ∈
    ((table.derive rule parent others).get (table.derivedRef rule parent others)).parents
  rw [Table.derived_lookup]
  simp [Node.parents]

/-- A generated record has the same non-orphan ancestry guarantee. -/
theorem TracesTo.generate {table : Table Site Rule} {parent : Ref table} {site : Site}
    (trace : TracesTo table parent site) (rule : Rule) (others : Array (Ref table) := #[]) :
    TracesTo (table.generate rule parent others) (table.generatedRef rule parent others) site := by
  apply TracesTo.parent (parent := table.lift _ _ parent) _ (trace.lift _ _)
  change parent.index.val ∈
    ((table.generate rule parent others).get (table.generatedRef rule parent others)).parents
  rw [Table.generated_lookup]
  simp [Node.parents]

end Parser.Provenance
