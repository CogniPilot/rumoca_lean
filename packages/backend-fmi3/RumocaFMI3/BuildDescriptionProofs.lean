import RumocaFMI3.BuildDescription
import XML.Certificate
import RumocaFMI3.IdentifierProofs

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
def Required (modelName : String) (p : Platform) (r : Decoded) : Prop :=
  r.identifier = "Rumoca_" ++ modelName ∧ r.platform = p.name ∧
  r.language = "C11" ∧ r.compiler = "gcc" ∧
  r.options = "-std=c11 -O2 -Wall -Wextra -Werror -Wno-unused-parameter -pedantic -fno-fast-math -ffp-contract=off -frounding-math" ∧
  r.sources = ["fmi3.c"] ∧ r.externalLibraries = ["m"]

/-- Independently specified native invocation, including the required math library. -/
def RequiredInvocation (sources headers output : String) (i : Invocation) : Prop :=
  i.compiler = "gcc" ∧ i.args =
    ["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", "-Wno-unused-parameter",
      "-pedantic", "-fno-fast-math", "-ffp-contract=off", "-frounding-math",
      "-fPIC", "-shared", "-DFMI3_OVERRIDE_FUNCTION_PREFIX", "-I", headers,
      sources ++ "/fmi3.c", "-lm", "-o", output]

/-- Actual XML text, uniquely selected recipes, and the matching producer invocation. -/
def ArtifactContract (modelName text : String) : Prop :=
  ∃ root : XML.Element, XML.Document root text ∧
    ∀ p : Platform, ∃ r : Decoded,
      decode root ("Rumoca_" ++ modelName) p.name = some r ∧ Required modelName p r ∧
      ∀ sources headers output, RequiredInvocation sources headers output
        (invocation modelName p sources headers output)

theorem recipe_required (modelName : String) (p : Platform) :
    Required modelName p (recipe modelName p).decoded := by
  simp [Required, recipe, Recipe.decoded, modelIdentifier]
  decide +kernel

theorem decode_recipe (modelName : String) (p : Platform) :
    decode (description modelName) (modelIdentifier modelName) p.name =
      some (recipe modelName p).decoded := by
  cases p <;> simp [decode, description, Recipe.xml, Recipe.decoded, recipe, only?, Platform.name,
    guard, List.filter, List.lookup, List.mapM_cons, List.mapM_nil]

theorem invocation_required (modelName : String) (p : Platform) (sources headers output : String) :
    RequiredInvocation sources headers output (invocation modelName p sources headers output) := by
  simp [RequiredInvocation, invocation, recipe, String.append_assoc]

set_option maxRecDepth 10000 in
theorem configuration_valid (modelName : String) (p : Platform)
    (text : XML.Text (modelIdentifier modelName)) : (recipe modelName p).xml.valid = true := by
  apply XML.Certificate.node_valid
  · rw [decide_eq_true_eq]
    refine ⟨?_, ?_, ?_, Or.inl rfl⟩
    · change XML.Name "BuildConfiguration"; decide +kernel
    · change XML.AttributesValid [("modelIdentifier", modelIdentifier modelName), ("platform", p.name)]
      constructor
      · change ["modelIdentifier", "platform"].Nodup; decide +kernel
      · intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · exact ⟨by change XML.Name "modelIdentifier"; decide +kernel, text⟩
        · cases p <;> dsimp only [Platform.name, Prod.fst, Prod.snd] <;>
            exact ⟨by decide +kernel, by decide +kernel⟩
    · change XML.Text ""; decide +kernel
  · cases p <;>
      simp only [Recipe.xml, recipe, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    all_goals
      repeat (rw [XML.Element.valid]; dsimp only [List.map, List.all, id])
      decide +kernel

theorem description_valid (modelName : String) (parts : NameParts modelName) :
    (description modelName).valid = true := by
  apply XML.Certificate.node_valid
  · rw [decide_eq_true_eq]
    refine ⟨?_, ?_, ?_, Or.inl rfl⟩
    · change XML.Name "fmiBuildDescription"; decide +kernel
    · change XML.AttributesValid [("fmiVersion", "3.0")]; decide +kernel
    · change XML.Text ""; decide +kernel
  · change ((recipe modelName .x86_64Linux).xml.valid &&
      ((recipe modelName .aarch64Linux).xml.valid && true)) = true
    rw [configuration_valid modelName .x86_64Linux (modelIdentifier_parts parts).text,
      configuration_valid modelName .aarch64Linux (modelIdentifier_parts parts).text]
    rfl

theorem artifact_correct (modelName : String) (parts : NameParts modelName) :
    ArtifactContract modelName (XML.document (description modelName)) := by
  refine ⟨description modelName, XML.document_correct _ (description_valid modelName parts), ?_⟩
  intro p
  exact ⟨(recipe modelName p).decoded, decode_recipe modelName p,
    recipe_required modelName p, invocation_required modelName p⟩

end Rumoca.FMI3.Build
