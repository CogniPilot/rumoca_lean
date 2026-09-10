import ProofAudit.Audit
import Parser.LALR.Generator
import Parser.LALR.Soundness
import Parser.LALR.EBNF

namespace Parser.LALRChecks
open LALR

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
-- `cbv` constructs proofs from defining equations; the kernel still checks
-- them. Suppress only its experimental-use advisory in the axiom-only report.
-- Direct kernel reduction cannot unfold Std's opaque accessibility proof for
-- List.merge, so computation here uses equations rather than native reduction.
set_option cbv.warning false

private def t (i : Nat) : Atom := .terminal i
private def n (i : Nat) : Atom := .nonterminal i

/-- S → ( S ) S | ε: genuine recursion and empty reductions. -/
def balanced : Grammar := ⟨2, 1, 0, #[⟨0, [t 0, n 0, t 1, n 0]⟩, ⟨0, []⟩]⟩

/-- E → E + T | T; T → ( E ) | id. -/
def expression : Grammar := ⟨4, 2, 0, #[
  ⟨0, [n 0, t 0, n 1]⟩, ⟨0, [n 1]⟩, ⟨1, [t 1, n 0, t 2]⟩, ⟨1, [t 3]⟩]⟩

/-- The standard LALR(1), non-SLR(1) assignment grammar. -/
def assignment : Grammar := ⟨3, 3, 0, #[
  ⟨0, [n 1, t 2, n 2]⟩, ⟨0, [n 2]⟩,
  ⟨1, [t 1, n 2]⟩, ⟨1, [t 0]⟩, ⟨2, [n 1]⟩]⟩

/-- Canonical LR(1) succeeds, but merging introduces a reduce/reduce conflict. -/
def lrOnly : Grammar := ⟨5, 3, 0, #[
  ⟨0, [t 0, n 1, t 3]⟩, ⟨0, [t 1, n 1, t 4]⟩,
  ⟨0, [t 0, n 2, t 4]⟩, ⟨0, [t 1, n 2, t 3]⟩,
  ⟨1, [t 2]⟩, ⟨2, [t 2]⟩]⟩

def ambiguous : Grammar := ⟨2, 1, 0, #[⟨0, [n 0, t 0, n 0]⟩, ⟨0, [t 1]⟩]⟩

private def failureName : LALR.Failure → String
  | .exhausted => "exhausted"
  | .rejected => "rejected"
  | .invalidTable => "invalid table"
  | .invalidTree => "invalid tree"

def observe (g : Grammar) (word : List Nat) (fuel : Nat := 500) : Except String (List Nat) := do
  let candidate ← generate g
  let tree ← (LALR.parse g candidate.tables fuel word).mapError failureName
  return tree.prependWord []

def stateCounts (g : Grammar) : Except String (Nat × Nat) := do
  let c ← generate g
  return (c.canonicalStates, c.collection.states.size)

theorem recursive_nullable :
    observe balanced [0, 0, 1, 0, 1, 1] = .ok [0, 0, 1, 0, 1, 1] ∧
    observe balanced [] = .ok [] := by constructor <;> cbv

theorem left_recursive :
    observe expression [3, 0, 1, 3, 0, 3, 2] = .ok [3, 0, 1, 3, 0, 3, 2] := by cbv

theorem merged_lookaheads : stateCounts assignment = .ok (14, 10) ∧
    observe assignment [1, 0, 2, 0] = .ok [1, 0, 2, 0] := by constructor <;> cbv

theorem canonical_only :
    (do let c ← canonical lrOnly; let _ ← buildTables lrOnly c; pure true) =
      Except.ok true ∧ (generate lrOnly).isOk = false := by constructor <;> cbv

theorem conflict_rejected : (generate ambiguous).isOk = false := by cbv

theorem malformed_input :
    (observe balanced [0, 1, 1]).isOk = false ∧
    (observe balanced [0]).isOk = false ∧
    (observe balanced [2]).isOk = false ∧
    (observe balanced [3]).isOk = false := by
  repeat' constructor
  all_goals cbv

theorem resource_distinct :
    observe balanced [] 0 = .error "exhausted" ∧
    (generate balanced ⟨1, 100⟩).isOk = false ∧
    (generate balanced ⟨100, 1⟩).isOk = false := by
  repeat' constructor
  all_goals cbv

theorem forged_tree_rejected :
    checkTree balanced [] (.node 0 0 []) = false ∧
    checkTree balanced [] (.node 1 1 []) = false ∧
    checkTree balanced [0] (.node 1 0 []) = false ∧
    checkTree balanced [] (.node 1 0 []) = true := by decide +kernel

theorem forged_table_rejected :
    (LALR.parse balanced ⟨#[#[none, none, some .accept]], #[#[none]]⟩ 2 []).isOk = false := by
  decide +kernel

private def result (tables : Tables) (input : List Nat) : Except LALR.Failure (List Nat) :=
  (LALR.parse balanced tables 4 input).map Tree.word

/-- Malformed tables must be distinguishable from ordinary syntax rejection. -/
theorem malformed_table_status :
    result ⟨#[], #[]⟩ [] = .error .invalidTable ∧
    result ⟨#[#[]], #[]⟩ [] = .error .invalidTable ∧
    result ⟨#[#[some (.shift 99), none, none]], #[]⟩ [0] = .error .invalidTable ∧
    result ⟨#[#[none, none, some (.shift 0)]], #[]⟩ [] = .error .invalidTable ∧
    result ⟨#[#[none, none, some (.reduce 99)]], #[]⟩ [] = .error .invalidTable ∧
    result ⟨#[#[none, none, some (.reduce 0)]], #[]⟩ [] = .error .invalidTable ∧
    result ⟨#[#[none, none, some (.reduce 1)]], #[]⟩ [] = .error .invalidTable ∧
    result ⟨#[#[none, none, some (.reduce 1)]], #[#[some 99]]⟩ [] = .error .invalidTable ∧
    result ⟨#[#[none, none, none]], #[#[none]]⟩ [] = .error .rejected := by decide +kernel

theorem recursive_ebnf :
    (do
      let p ← Frontend.compile "s : '(' s ')' s | '';"
      observe p.grammar [0, 0, 1, 1]) = .ok [0, 0, 1, 1] := by cbv

theorem optional_many :
    (do
      let p ← Frontend.compile "s : ['a'] {'b'};"
      observe p.grammar [0, 1, 1]) = .ok [0, 1, 1] := by cbv

theorem undefined_rule : (Frontend.compile "s : missing;").isOk = false := by decide +kernel

#audit axioms recursive_nullable
#audit axioms left_recursive
#audit axioms merged_lookaheads
#audit axioms canonical_only
#audit axioms conflict_rejected
#audit axioms malformed_input
#audit axioms resource_distinct
#audit axioms forged_tree_rejected
#audit axioms forged_table_rejected
#audit axioms malformed_table_status
#audit axioms recursive_ebnf
#audit axioms optional_many
#audit axioms undefined_rule

end Parser.LALRChecks
