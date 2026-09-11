import Parser.Provenance

/-! A consuming stage can own its rule vocabulary while retaining every input
site, edge and reference index. This changes rule labels only; it does not
invent source spans or rely on an injective source-content hash. -/
namespace Parser.Provenance

def Node.mapRule (map : Rule → TargetRule) : Node Site Rule → Node Site TargetRule
  | .source site => .source site
  | .derived rule parent others => .derived (map rule) parent others
  | .generated rule parent others => .generated (map rule) parent others

theorem Node.mapRule_parents (map : Rule → TargetRule) (node : Node Site Rule) :
    (node.mapRule map).parents = node.parents := by cases node <;> rfl

theorem Node.mapRule_source (map : Rule → TargetRule) (node : Node Site Rule) (site : Site) :
    node.mapRule map = .source site ↔ node = .source site := by cases node <;> simp [mapRule]

def Table.mapRule (table : Table Site Rule) (map : Rule → TargetRule) : Table Site TargetRule where
  nodes := table.nodes.map (Node.mapRule map)
  prior := by
    intro index bound parent member
    simp only [Array.getElem_map, Node.mapRule_parents] at member
    exact table.prior index (by simpa using bound) parent member

def Table.mapRef (table : Table Site Rule) (map : Rule → TargetRule) (ref : Ref table) :
    Ref (table.mapRule map) :=
  ⟨⟨ref.index.val, by simp [mapRule]⟩⟩

def Table.unmapRef (table : Table Site Rule) (map : Rule → TargetRule)
    (ref : Ref (table.mapRule map)) : Ref table :=
  ⟨⟨ref.index.val, by simpa [mapRule] using ref.index.isLt⟩⟩

theorem Table.unmap_mapRef (table : Table Site Rule) (map : Rule → TargetRule) (ref : Ref table) :
    table.unmapRef map (table.mapRef map ref) = ref := rfl

theorem Table.map_unmapRef (table : Table Site Rule) (map : Rule → TargetRule)
    (ref : Ref (table.mapRule map)) : table.mapRef map (table.unmapRef map ref) = ref := rfl

theorem Table.get_mapRef (table : Table Site Rule) (map : Rule → TargetRule) (ref : Ref table) :
    (table.mapRule map).get (table.mapRef map ref) = (table.get ref).mapRule map := by
  simp [get, mapRule, mapRef]

theorem Table.get_unmapRef (table : Table Site Rule) (map : Rule → TargetRule)
    (ref : Ref (table.mapRule map)) :
    (table.get (table.unmapRef map ref)).mapRule map = (table.mapRule map).get ref := by
  simpa only [Table.map_unmapRef] using (table.get_mapRef map (table.unmapRef map ref)).symm

theorem TracesTo.mapRule {table : Table Site Rule} {ref : Ref table} {site : Site}
    (trace : TracesTo table ref site) (map : Rule → TargetRule) :
    TracesTo (table.mapRule map) (table.mapRef map ref) site := by
  induction trace with
  | source found =>
    apply TracesTo.source
    rw [table.get_mapRef, found]
    rfl
  | @parent ref parent site member trace ih =>
    apply TracesTo.parent (parent := table.mapRef map parent) _ ih
    change parent.index.val ∈ ((table.mapRule map).get (table.mapRef map ref)).parents
    rw [table.get_mapRef, Node.mapRule_parents]
    exact member

/-- Reflection needs no injectivity of the rule map: rule labels cannot add
or remove graph edges, or change a source leaf into a generated node. -/
theorem TracesTo.unmapRule {table : Table Site Rule} (map : Rule → TargetRule)
    {ref : Ref (table.mapRule map)} {site : Site}
    (trace : TracesTo (table.mapRule map) ref site) :
    TracesTo table (table.unmapRef map ref) site := by
  induction trace with
  | @source ref site found =>
    apply TracesTo.source
    exact (Node.mapRule_source map _ site).mp ((table.get_unmapRef map _).trans found)
  | @parent ref parent site member trace ih =>
    apply TracesTo.parent (parent := table.unmapRef map parent) _ ih
    change parent.index.val ∈ (table.get (table.unmapRef map ref)).parents
    rw [← Node.mapRule_parents map, table.get_unmapRef]
    exact member

theorem Table.mapRule_traces_iff (table : Table Site Rule) (map : Rule → TargetRule)
    (ref : Ref table) (site : Site) :
    TracesTo (table.mapRule map) (table.mapRef map ref) site ↔ TracesTo table ref site :=
  ⟨fun trace => trace.unmapRule map, fun trace => trace.mapRule map⟩

end Parser.Provenance
