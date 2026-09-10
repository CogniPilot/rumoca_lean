import Std

namespace Parser

/-- Tail-recursive table execution, independent of grammar analysis and mathlib. -/
def runDFA (next : σ → α → σ) (final : σ → Bool) (state : σ) : List α → Bool
  | [] => final state
  | c :: cs => runDFA next final (next state c) cs

end Parser
