import ModelicaParser.OriginProofs
import ModelicaParser.LocatedTotal

/-! The source context owned by actual IR occurrences. A semantic AST alone is
insufficient: construction requires its checked parse and actual input identity. -/
namespace Rumoca.Provenance
open _root_.Parser

/-- These identifiers name the transformations of the admitted scalar core.
They are not an extensible string fallback for unsupported compiler actions. -/
inductive Rule where
  | derivativeCoordinate
  | equationResidual
  | solveUnitDerivative
  | returnDerivative
  | realStartFallback
  | selectUnfixedStart
  | algorithmAdmission
  | unitSamplingPeriod
  | samplingPeriodValue
  | algorithmStartup
  | algorithmStateInitialization
  | algorithmStateWrite
  | algorithmRecalibrate
  | algorithmDoStep
  | algorithmStateRead
  | unitAlgorithmIncrement
  | unitAlgorithmStep
  | algorithmStateUpdate
  | algorithmPeriodInitialization
  | algorithmPeriodWrite
  deriving Repr, DecidableEq

structure Context (model : AST.Model) where
  input : Source.InputRef
  sites : Array (_root_.Parser.Provenance.SourceRef input.inputs)
  /-- The parse witness is erased. Origin metadata need not keep token lists or
  an entire parse tree alive after constructing the concrete source sites. -/
  correspondence : ∃ parsed : LocatedParsed input.source,
    parsed.parsed.ast = model ∧ sites = Origins.sites input.inputs input.file parsed

def Context.ofLocated (input : Source.InputRef) (parsed : LocatedParsed input.source) :
    Context parsed.parsed.ast :=
  ⟨input, Origins.sites input.inputs input.file parsed, ⟨parsed, rfl, rfl⟩⟩

theorem Context.site_count (context : Context model) : context.sites.size = 9 := by
  obtain ⟨parsed, _, sites⟩ := context.correspondence
  rw [sites]
  simp [Origins.sites]

abbrev Table (context : Context model) :=
  _root_.Parser.Provenance.Table (_root_.Parser.Provenance.SourceRef context.input.inputs) Rule

def Context.origins (context : Context model) : Table context :=
  _root_.Parser.Provenance.Table.fromSources context.sites

def Context.site (context : Context model) (field : Origins.Field) :
    _root_.Parser.Provenance.SourceRef context.input.inputs :=
  context.sites[field.index.val]'(by rw [context.site_count]; exact field.index.isLt)

def Context.ref (context : Context model) (field : Origins.Field) :
    _root_.Parser.Provenance.Ref context.origins :=
  ⟨⟨field.index.val, by simp [origins, _root_.Parser.Provenance.Table.fromSources, context.site_count]⟩⟩

theorem Context.lookup (context : Context model) (field : Origins.Field) :
    context.origins.get (context.ref field) = .source (context.site field) := by
  simp [origins, ref, site, _root_.Parser.Provenance.Table.get,
    _root_.Parser.Provenance.Table.fromSources]

/-- The compact sites retain the actual parser's field correspondence even
though the parsing witness itself is not stored in native origin metadata. -/
theorem Context.source_fields (context : Context model) :
    ∃ parsed : LocatedParsed context.input.source, parsed.parsed.ast = model ∧
      ∀ field, context.site field = Origins.site context.input.inputs context.input.file parsed field := by
  obtain ⟨parsed, source, sites⟩ := context.correspondence
  refine ⟨parsed, source, ?_⟩
  intro field
  cases field <;> simp [site, sites, Origins.sites, Origins.Field.index] <;> rfl

end Rumoca.Provenance
