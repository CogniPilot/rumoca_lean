import ProofAudit.Audit
import Parser.LALR.SafetyProofs
import Parser.LALR.Soundness

namespace Parser.LRSafetyChecks
open LALR

def grammar : Grammar := ⟨1, 1, 0, #[⟨0, [.terminal 0]⟩]⟩

def tables : Tables := ⟨
  #[#[some (.shift 1), none], #[none, some (.reduce 0)], #[none, some .accept]],
  #[#[some 2], #[none], #[none]]⟩

def edges : List Edge := [⟨0, .terminal 0, 1⟩, ⟨0, .nonterminal 0, 2⟩]

theorem certificate : Safety.validate grammar tables edges = true := by decide +kernel

/-- A genuine instance of the universal theorem, for arbitrary words/fuel. -/
theorem all_runs (h : run grammar tables fuel ⟨[], input⟩ = .error error) :
    error = .exhausted ∨ error = .rejected := Safety.validated_run_safe certificate h

theorem public_parser (h : LALR.parse grammar tables fuel input = .error error) :
    error = .exhausted ∨ error = .rejected := Safety.validated_parse_safe certificate h

private def setAction (q a : Nat) (action : Option Action) : Tables :=
  { tables with
    actions := tables.actions.setIfInBounds q ((tables.actions[q]?.getD #[]).setIfInBounds a action) }

theorem missing_edge : Safety.validate grammar tables [⟨0, .terminal 0, 1⟩] = false ∧
    Safety.validate grammar tables [⟨0, .nonterminal 0, 2⟩] = false := by decide +kernel

theorem wrong_labels : Safety.validate grammar tables
    [⟨0, .nonterminal 0, 1⟩, ⟨0, .nonterminal 0, 2⟩] = false := by decide +kernel

theorem invalid_targets : Safety.validate grammar (setAction 0 0 (some (.shift 99)))
    (⟨0, .terminal 0, 99⟩ :: edges) = false ∧
    Safety.validate grammar (setAction 0 0 (some (.shift 0)))
    (⟨0, .terminal 0, 0⟩ :: edges) = false := by decide +kernel

theorem invalid_reductions :
    Safety.validate grammar (setAction 0 1 (some (.reduce 0))) edges = false ∧
    Safety.validate grammar (setAction 1 1 (some (.reduce 1))) edges = false := by decide +kernel

theorem missing_goto : Safety.validate grammar
    { tables with gotos := #[#[none], #[none], #[none]] } edges = false := by decide +kernel

theorem premature_acceptance : Safety.validate grammar (setAction 1 1 (some .accept)) edges = false ∧
    Safety.validate grammar (setAction 0 1 (some .accept)) edges = false ∧
    Safety.validate grammar (setAction 2 0 (some .accept)) edges = false := by decide +kernel

theorem eof_shift : Safety.validate grammar (setAction 0 1 (some (.shift 1)))
    (⟨0, .terminal 1, 1⟩ :: edges) = false := by decide +kernel

/-- A second route to the reduction state needs a different return goto.
Neither omitting that edge nor supplying it can conceal the unsafe path. -/
def additionalPathTables : Tables :=
  { tables with actions := #[#[some (.shift 1), none],
      #[some (.reduce 0), some (.reduce 0)], #[some (.shift 1), some .accept]] }

theorem additional_path :
    Safety.validate grammar additionalPathTables edges = false ∧
    Safety.validate grammar additionalPathTables
      (⟨2, .terminal 0, 1⟩ :: edges) = false ∧
    (run grammar additionalPathTables 10 ⟨[], [0, 0]⟩).map Tree.word =
      .error .invalidTable := by decide +kernel

/-- A table that rejects every input is safe but incomplete. This prevents
the safety certificate from being advertised as the full parsing contract. -/
def rejectAll : Tables := ⟨#[#[none, none]], #[#[none]]⟩

theorem safety_is_not_completeness :
    Safety.validate grammar rejectAll [] = true ∧
    (LALR.parse grammar rejectAll 10 [0]).isOk = false ∧ grammar.Accepts [0] := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  exact (checkTree_sound grammar [0] (.node 0 0 [.terminal 0]) (by decide +kernel)).2.2

#audit axioms certificate
#audit axioms all_runs
#audit axioms public_parser
#audit axioms missing_edge
#audit axioms wrong_labels
#audit axioms invalid_targets
#audit axioms invalid_reductions
#audit axioms missing_goto
#audit axioms premature_acceptance
#audit axioms eof_shift
#audit axioms additional_path
#audit axioms safety_is_not_completeness

end Parser.LRSafetyChecks
