import Rumoca.InitializationDiagnostics
import RumocaCore.Initialization.DiagnosticProofs

namespace Rumoca

/-- Compiler notices agree with the shared editor analysis for the same
immutable input and parse, without a second parse or a location fallback. -/
theorem Artifact.initializationDiagnostics_eq_forModel (artifact : Artifact input) :
    artifact.initializationDiagnostics =
      Initialization.forModel input artifact.located artifact.solve.dae.flat.resolved := by
  dsimp only [initializationDiagnostics, Initialization.forModel]
  rw [artifact.solve.initial_default, Solve.Model.initial_default]
  rfl

/-- Every notice is retained using the artifact's required source provenance. -/
theorem Artifact.initializationDiagnostic_count (artifact : Artifact source) :
    artifact.initializationDiagnostics.length = artifact.solve.initial.notices.length := by
  simp [initializationDiagnostics, Initialization.diagnostics]

theorem Artifact.initializationDiagnostic_state (artifact : Artifact source)
    (diagnostic : Parser.Source.Diagnostic source.source)
    (member : diagnostic ∈ artifact.initializationDiagnostics) :
    diagnostic.span.text = artifact.parsed.ast.state := by
  have span := Initialization.diagnostics_span _ _ _ diagnostic member
  rw [span]
  exact artifact.located.state_field_text

/-! ### Constant-rate notices -/

/-- The identifier of the `i`-th `Real ident ;` declaration of a constant-rate
source is token `3 + 3 i`. -/
theorem ConstantProfile.Model.state_token (m : ConstantProfile.Model) (i : Nat) (state : String)
    (found : m.states[i]? = some state) : m.tokens[3 + 3 * i]? = some (.ident state) := by
  have decls : ∀ (ss : List String) (i : Nat) (rest : List _root_.Parser.Token), ss[i]? = some state →
      (ss.flatMap ConstantProfile.declTokens ++ rest)[1 + 3 * i]? = some (.ident state) := by
    intro ss
    induction ss with
    | nil => intro i rest h; simp at h
    | cons s ss ih =>
      intro i rest h
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        subst h
        rfl
      | succ i =>
        simp only [List.getElem?_cons_succ] at h
        have step := ih i rest h
        simp only [List.flatMap_cons, ConstantProfile.declTokens, List.cons_append, List.nil_append]
        rw [show 1 + 3 * (i + 1) = (1 + 3 * i) + 1 + 1 + 1 by omega]
        simpa using step
  have := decls m.states i ([.literal "equation"] ++
    (m.equations.flatMap ConstantProfile.equationTokens) ++
      [.literal "end", .ident m.endName, .literal ";"]) found
  simp only [ConstantProfile.Model.tokens, List.cons_append, List.nil_append, List.append_assoc]
    at this ⊢
  rw [show 3 + 3 * i = (1 + 3 * i) + 1 + 1 by omega]
  simpa using this

/-- Each constant-rate declaration span covers exactly the state's identifier. -/
theorem ConstantArtifact.state_span (a : ConstantArtifact input) (i : Nat) (state : String)
    (found : a.prepared.parsed.parsed.ast.states[i]? = some state) :
    (a.prepared.parsed.tokenSpan (3 + 3 * i)).text = state := by
  exact Modelica.Selection.LocatedParsed.tokenSpan_record a.prepared.parsed (3 + 3 * i) (.ident state)
    (a.prepared.parsed.parsed.ast.state_token i state found)

/-- Every constant-rate notice is a §8.6 notice of one declared state, located
at that state's identifier. -/
theorem ConstantArtifact.initializationDiagnostic_state (a : ConstantArtifact input)
    (diagnostic : Parser.Source.Diagnostic input.source)
    (member : diagnostic ∈ a.initializationDiagnostics) :
    ∃ state ∈ a.prepared.parsed.parsed.ast.states, diagnostic.span.text = state ∧
      ∃ notice ∈ [Initialization.Notice.fallbackUsed, .unfixedStartSelected],
        diagnostic.message = notice.message state 0 := by
  obtain ⟨⟨state, i⟩, entry, inner⟩ := List.mem_flatMap.mp member
  have found := List.mk_mem_zipIdx_iff_getElem?.mp entry
  obtain ⟨notice, noticeMember, rfl⟩ := List.mem_map.mp inner
  exact ⟨state, List.mem_of_getElem? found, a.state_span i state found, notice,
    by simpa [ConstantProfile.Model.plan_default] using noticeMember,
    by simp [ConstantProfile.Model.plan_default]⟩

/-- Every declared state carries both §8.6 notices at its identifier: the
fallback start is used, and the unfixed start is selected as fixed. -/
theorem ConstantArtifact.initializationDiagnostic_notices (a : ConstantArtifact input)
    (state : String) (declared : state ∈ a.prepared.parsed.parsed.ast.states)
    (notice : Initialization.Notice)
    (listed : notice ∈ [Initialization.Notice.fallbackUsed, .unfixedStartSelected]) :
    ∃ diagnostic ∈ a.initializationDiagnostics,
      diagnostic.span.text = state ∧ diagnostic.message = notice.message state 0 := by
  obtain ⟨i, bound, rfl⟩ := List.getElem_of_mem declared
  have found : a.prepared.parsed.parsed.ast.states[i]? = some a.prepared.parsed.parsed.ast.states[i] :=
    List.getElem?_eq_getElem bound
  refine ⟨⟨"initialization", a.prepared.parsed.tokenSpan (3 + 3 * i),
    notice.message a.prepared.parsed.parsed.ast.states[i] 0, []⟩, ?_, a.state_span i _ found, rfl⟩
  refine List.mem_flatMap.mpr ⟨(a.prepared.parsed.parsed.ast.states[i], i),
    List.mk_mem_zipIdx_iff_getElem?.mpr found, ?_⟩
  exact List.mem_map.mpr ⟨notice, by simpa [ConstantProfile.Model.plan_default] using listed,
    by simp [ConstantProfile.Model.plan_default]⟩

/-- Two notices are reported per declared state. -/
theorem ConstantArtifact.initializationDiagnostic_count (a : ConstantArtifact input) :
    a.initializationDiagnostics.length = 2 * a.prepared.parsed.parsed.ast.states.length := by
  simp only [ConstantArtifact.initializationDiagnostics, List.length_flatMap, Initialization.diagnostics,
    List.length_map, ConstantProfile.Model.plan_default, List.length_cons, List.length_nil]
  simp [List.map_const', List.sum_replicate, Nat.mul_comm]

end Rumoca
