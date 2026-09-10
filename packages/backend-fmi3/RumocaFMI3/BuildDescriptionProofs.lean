import RumocaFMI3.BuildDescription
import XML.Proofs

namespace Rumoca.FMI3.Build

/-- Require a unique matching configuration or source set. -/
def only? : List α → Option α
  | [x] => some x
  | _ => none

structure Decoded where
  identifier : String
  platform : String
  language : String
  compiler : String
  options : String
  sources : List String
  externalLibraries : List String
  deriving DecidableEq, Repr

/-- Observe XML attributes independently of the renderer. The contract also
checks the complete source/library lists and exact option string. -/
def decode (root : XML.Element) (identifier platform : String) : Option Decoded := do
  guard (root.name == "fmiBuildDescription")
  guard (root.attributes.lookup "fmiVersion" == some "3.0")
  let config ← only? (root.children.filter fun e => e.name == "BuildConfiguration" &&
    e.attributes.lookup "modelIdentifier" == some identifier &&
    e.attributes.lookup "platform" == some platform)
  let set ← only? (config.children.filter (·.name == "SourceFileSet"))
  guard (config.children.all fun e => e.name == "SourceFileSet" || e.name == "Library")
  let language ← set.attributes.lookup "language"
  let compiler ← set.attributes.lookup "compiler"
  let options ← set.attributes.lookup "compilerOptions"
  let sources ← set.children.mapM fun e => do
    guard (e.name == "SourceFile" && e.children.isEmpty && e.text.isEmpty)
    e.attributes.lookup "name"
  let libraries ← (config.children.filter (·.name == "Library")).mapM fun e => do
    guard (e.attributes.lookup "external" == some "true" && e.children.isEmpty && e.text.isEmpty)
    e.attributes.lookup "name"
  return ⟨identifier, platform, language, compiler, options, sources, libraries⟩

def Recipe.decoded (r : Recipe) : Decoded :=
  ⟨r.identifier, r.platform, r.language, r.compiler, String.intercalate " " r.options,
    r.sources, r.externalLibraries⟩

/-- Independently stated obligations of the current Linux/GCC binary64 C profile.
These are build requirements, not a proof about GCC or its output machine code. -/
def Required (p : Platform) (r : Decoded) : Prop :=
  r.identifier = "RumocaModel" ∧ r.platform = p.name ∧
  r.language = "C11" ∧ r.compiler = "gcc" ∧
  r.options = "-std=c11 -O2 -Wall -Wextra -Werror -Wno-unused-parameter -pedantic -fno-fast-math -ffp-contract=off -frounding-math" ∧
  r.sources = ["model.c", "fmi3.c"] ∧ r.externalLibraries = ["m"]

/-- Independently specified native invocation, including the required math library. -/
def RequiredInvocation (sources headers output : String) (i : Invocation) : Prop :=
  i.compiler = "gcc" ∧ i.args =
    ["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", "-Wno-unused-parameter",
      "-pedantic", "-fno-fast-math", "-ffp-contract=off", "-frounding-math",
      "-fPIC", "-shared", "-I", headers,
      sources ++ "/model.c", sources ++ "/fmi3.c", "-lm", "-o", output]

/-- Actual XML text, uniquely selected recipes, and the matching producer invocation. -/
def ArtifactContract (text : String) : Prop :=
  ∃ root : XML.Element, XML.Document root text ∧
    ∀ p : Platform, ∃ r : Decoded,
      decode root "RumocaModel" p.name = some r ∧ Required p r ∧
      ∀ sources headers output, RequiredInvocation sources headers output
        (invocation p sources headers output)

theorem recipe_required (p : Platform) : Required p (recipe p).decoded := by
  cases p <;> unfold Required <;> decide +kernel

theorem decode_recipe (p : Platform) :
    decode description "RumocaModel" p.name = some (recipe p).decoded := by
  cases p <;> decide +kernel

theorem invocation_required (p : Platform) (sources headers output : String) :
    RequiredInvocation sources headers output (invocation p sources headers output) := by
  simp [RequiredInvocation, invocation, recipe, String.append_assoc]

set_option maxRecDepth 10000 in
theorem description_valid : description.valid = true := by
  simp only [description, Recipe.xml, recipe, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  repeat (rw [XML.Element.valid]; dsimp only [List.map, List.all, id])
  decide +kernel

theorem artifact_correct : ArtifactContract (XML.document description) := by
  refine ⟨description, XML.document_correct _ description_valid, ?_⟩
  intro p
  exact ⟨(recipe p).decoded, decode_recipe p, recipe_required p, invocation_required p⟩

end Rumoca.FMI3.Build
