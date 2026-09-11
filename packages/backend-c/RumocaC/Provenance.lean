import RumocaCore.Provenance.Source
import Parser.ProvenanceMapping

/-! C emission owns its generation rules. The upstream vocabulary is embedded
without modifying it; graph conversion preserves all source sites and edges. -/
namespace Rumoca.CProvenance

inductive Rule where
  | upstream (rule : Provenance.Rule)
  | initialLiteral
  | initialConversion
  | stateStorage
  | initializeState
  deriving Repr, DecidableEq

abbrev Table (context : Provenance.Context source) :=
  _root_.Parser.Provenance.Table
    (_root_.Parser.Provenance.SourceRef context.input.inputs) Rule

def fromCore (table : Provenance.Table context) : Table context := table.mapRule Rule.upstream

theorem fromCore_traces_iff (table : Provenance.Table context)
    (ref : _root_.Parser.Provenance.Ref table) (site) :
    _root_.Parser.Provenance.TracesTo (fromCore table) (table.mapRef Rule.upstream ref) site ↔
      _root_.Parser.Provenance.TracesTo table ref site :=
  table.mapRule_traces_iff Rule.upstream ref site

end Rumoca.CProvenance
