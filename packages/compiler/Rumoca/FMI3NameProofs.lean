import Rumoca.Compiler
import RumocaFMI3.IdentifierProofs

namespace Rumoca.FMI3
open _root_.Parser

/-- Source character rules, rather than a producer's asserted name validity,
establish the C namespace's lexical precondition. -/
theorem lexed_name (h : Rumoca.Lexes chars tokens) (mem : Token.ident name ∈ tokens) :
    NameParts name := by
  induction h with
  | nil => simp at mem
  | space _ _ ih => exact ih mem
  | @ident c ts cs hs hi h ih =>
    rcases List.mem_cons.mp mem with hm | hm
    · unfold classifyWord at hm
      split at hm
      · cases hm
      · have eq := Token.ident.inj hm
        subst name
        exact ⟨c, cs.takeWhile identRest, String.toList_ofList, hi, List.all_takeWhile⟩
    · exact ih hm
  | number _ _ _ _ ih =>
    rcases List.mem_cons.mp mem with hm | hm
    · refine absurd hm ?_
      unfold numberToken
      split
      · simp
      · split <;> simp
    · exact ih hm
  | punct _ _ _ _ _ ih | dotmul _ ih =>
    rcases List.mem_cons.mp mem with hm | hm
    · cases hm
    · exact ih hm

theorem parsed_name (p : Parsed source) : NameParts p.ast.name :=
  lexed_name (parsed_lexes p) (by simp [AST.Model.tokens])

theorem parsed_modelIdentifier (p : Parsed source) :
    CIdentifier.valid [] (modelIdentifier p.ast.name) = true :=
  modelIdentifier_valid (parsed_name p)

theorem parsed_functionPrefix (p : Parsed source) :
    CIdentifier.valid [] (modelIdentifier p.ast.name ++ "_") = true :=
  functionPrefix_word (parsed_name p)

end Rumoca.FMI3
