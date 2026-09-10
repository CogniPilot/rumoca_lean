import Rumoca.Semantics
import RumocaC.Execution
import Rumoca.Behavioral

open _root_.Parser

/-! A single Lean contract from the compiled source and emitted C bytes to
terminating binary64 execution and its relation to the real ODE. The C grammar
and IEEE interpretation are authored specifications; machine compilation and
the host ABI are outside this theorem. -/
noncomputable section
namespace Rumoca

structure ExecutionContract (p : CSyntax.Program) (m : AST.Model)
    (x : Binary64.Value) (n : Nat) : Prop where
  source_solution : Source.Solves m (Source.trajectory (Binary64.value x))
  initial_value : Source.trajectory (Binary64.value x) 0 = Binary64.value x
  terminates : CExecution.Reaches p (.entry .sample x n) (.returned (Binary64.run x n))
  all_terminate : Acc (fun t s => CExecution.Step p s t) (.entry .sample x n)
  all_complete : ∀ s, CExecution.Reaches p (.entry .sample x n) s →
    CExecution.Reaches p s (.returned (Binary64.run x n))
  unique_result : ∀ y, CExecution.Reaches p (.entry .sample x n) (.returned y) → y = Binary64.run x n
  rounding_error : |Binary64.value (Binary64.run x n) -
    Source.trajectory (Binary64.value x) (n : ℝ)| ≤ n
  counter_safe : n < 2 ^ 64 → ∀ s, CExecution.Reaches p (.entry .sample x n) s →
    CExecution.counter s < 2 ^ 64

theorem execution_correct (m : Solve.Model source) (x : Binary64.Value) (n : Nat) :
    ExecutionContract (CExecution.program m) source x n := by
  refine ⟨Source.trajectory_solves _ m.dae.flat.resolved _, ?_,
    CExecution.sample_reaches m x n, CExecution.sample_accessible m x n,
    fun _ h => CExecution.sample_all_executions m x n h,
    fun _ h => CExecution.sample_result_unique m x n h,
    Binary64.run_error x n, ?_⟩
  · simp [Source.trajectory]
  · intro hn s h
    exact CExecution.counter_in_range h hn

/-- This binds the independently interpreted C body to the entire lowering chain.
The lexical witness refers to the actual source characters, and the target
grammar witness refers to the actual emitted characters. -/
structure ArtifactContract (a : Artifact source) (emitted : String) : Prop where
  bytes : a.cSource = emitted
  source_lexes : Lexes source.toList a.parsed.ast.tokens
  source_ebnf : Generated.rawGrammar.Accepts (a.parsed.tokens.map Token.symbol)
  c_grammar : CSyntax.Denotes emitted (CExecution.program a.solve)
  rhs_preserved : ∀ d input, Source.Equation a.parsed.ast d ↔
    d a.parsed.ast.state = C.eval (input : ℝ) a.target.rhs
  execution : ∀ x n, ExecutionContract (CExecution.program a.solve) a.parsed.ast x n
  well_scoped : CStatements.WellScoped (CExecution.program a.solve)
  statements : ∃ chars, emitted.toList = C.preamble.toList ++ chars ∧
    CSyntax.Lexes chars (CStatements.programTokens (CExecution.program a.solve))
  behaviors : ∀ f x n b,
    (CStatements.machine (CExecution.program a.solve)).Behaves (.entry f x n) b ↔
      Source.SampledBehavior a.parsed.ast f x n.val b
  call_termination : ∀ f x n,
    Acc (fun t s => CStatements.Step (CExecution.program a.solve) s t) (.entry f x n)
  call_completion : ∀ f x n s,
    CStatements.Reaches (CExecution.program a.solve) (.entry f x n) s →
    CStatements.Reaches (CExecution.program a.solve) s
      (.returned (CStatements.result a.solve f x n))
  real_solution_refinement : ∀ f x n y,
    Source.Solves a.parsed.ast f → f 0 = Binary64.value x →
    (CStatements.machine (CExecution.program a.solve)).Behaves
      (.entry .sample x n) (.terminates y) →
    |Binary64.value y - f n.val| ≤ n.val
  model_exchange : ∀ x n b,
    (CStatements.machine (CExecution.program a.solve)).Behaves (.entry .rhs x n) b ↔
      b = .terminates (ModelExchange.derivative a.solve ⟨x⟩)
  co_simulation : ∀ x n b,
    (CStatements.machine (CExecution.program a.solve)).Behaves (.entry .sample x n) b ↔
      b = .terminates ((CoSimulation.run a.solve ⟨⟨x⟩, 0⟩ n.val).model.x)

theorem artifact_correct (a : Artifact source) (he : a.cSource = emitted) :
    ArtifactContract a emitted := by
  have hp : CSyntax.Denotes emitted (CExecution.program a.solve) :=
    he ▸ CSyntax.module_render a.target
  exact ⟨he, parsed_lexes a.parsed, parsed_in_ebnf a.parsed, hp,
    compiler_correct a.solve, execution_correct a.solve, CStatements.lower_scoped a.solve,
    CStatements.denotes_statements hp, CStatements.lower_behavior_correct a.solve,
    CStatements.all_terminate a.solve, fun f x n _ h => CStatements.all_complete a.solve f x n h,
    (fun _ x n _ hf hi hb => CStatements.real_refinement a.solve x n hf hi hb),
    CStatements.model_exchange_correct a.solve, CStatements.co_simulation_correct a.solve⟩

/-- The actual compiler result, actual emitted text and semantic contract are
checked together. No cross-prover assumption or native Float axiom is used. -/
theorem compile_verified (h : compile source = .ok a) (he : a.cSource = emitted) :
    compile source = .ok a ∧ ArtifactContract a emitted :=
  ⟨h, artifact_correct a he⟩

/-- Whole-compiler semantic preservation at the C boundary. Every behavior of
the actual emitted output is a source numerical-profile behavior, and conversely.
Inputs use actual finite IEEE bit patterns and an actual 64-bit unsigned count.
The separate real-solution refinement is part of `compile_verified`. -/
theorem compiler_semantic_preservation (h : compile source = .ok a) (he : a.cSource = emitted) :
    ∃ p, CSyntax.Denotes emitted p ∧ CStatements.WellScoped p ∧
      ∀ f (bits : Binary64.FiniteBits) (n : CStatements.Counter) b,
        (CStatements.machine p).Behaves (.entry f (Binary64.ofBits bits) n) b ↔
          Source.SampledBehavior a.parsed.ast f (Binary64.ofBits bits) n.val b := by
  have hc := (compile_verified h he).2
  exact ⟨CExecution.program a.solve, hc.c_grammar, hc.well_scoped,
    fun f bits n b => hc.behaviors f (Binary64.ofBits bits) n b⟩

/-- Transfer any property of source-profile observations to every behavior of
the actual emitted output. The property can constrain returned bits or rule out
wrong/diverging executions; it is not restricted to a numeric error bound. -/
theorem compiler_preserves_property (h : compile source = .ok a) (he : a.cSource = emitted)
    (hp : CSyntax.Denotes emitted p) (f : Profile.Function)
    (bits : Binary64.FiniteBits) (n : CStatements.Counter)
    (property : Transition.Observation Binary64.Value → Prop)
    (hs : ∀ b, Source.SampledBehavior a.parsed.ast f (Binary64.ofBits bits) n.val b → property b) :
    ∀ b, (CStatements.machine p).Behaves (.entry f (Binary64.ofBits bits) n) b → property b := by
  obtain ⟨q, hq, _, hb⟩ := compiler_semantic_preservation h he
  cases CSyntax.denotes_unique hp hq
  exact fun b ht => hs b ((hb f bits n b).mp ht)

end Rumoca
