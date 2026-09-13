import Rumoca.FMI3NameProofs
import RumocaFMI3.IdentityNames

/-! Derive token byte validity from the actual parsed source and the dependent
Solve/FMI preparation. This does not assume the emitter's token is valid. -/
namespace Rumoca.FMI3
open _root_.Parser CStringMemory

theorem parsed_state_name (parsed : Parsed source) : NameParts parsed.ast.state :=
  lexed_name (parsed_lexes parsed) (by simp [AST.Model.tokens])

theorem compiled_token_ascii (artifact : Artifact input) :
    NonzeroASCII (token artifact.solve.prepareFMI3) :=
  Identity.token_ascii artifact.solve.prepareFMI3
    (parsed_name artifact.parsed) (parsed_state_name artifact.parsed)

theorem compiled_token_content (artifact : Artifact input) :
    content (token artifact.solve.prepareFMI3) = (token artifact.solve.prepareFMI3).toUTF8.data.toList :=
  (compiled_token_ascii artifact).content

end Rumoca.FMI3
