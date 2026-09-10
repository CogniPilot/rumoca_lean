import XML.Basic

namespace Rumoca.FMI3

def modelIdentifier : String := "RumocaModel"

namespace Build

/-- The currently supported source-build profiles. No unspecified-platform fallback. -/
inductive Platform where
  | x86_64Linux | aarch64Linux
  deriving DecidableEq, Repr

def Platform.name : Platform → String
  | .x86_64Linux => "x86_64-linux"
  | .aarch64Linux => "aarch64-linux"

/-- Shared compile/link data. Packaging supplies only paths and shared-object flags. -/
structure Recipe where
  identifier : String
  platform : String
  language : String
  compiler : String
  options : List String
  sources : List String
  externalLibraries : List String
  deriving DecidableEq, Repr

def recipe (p : Platform) : Recipe :=
  ⟨modelIdentifier, p.name, "C11", "gcc",
    ["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", "-Wno-unused-parameter",
      "-pedantic", "-fno-fast-math", "-ffp-contract=off", "-frounding-math"],
    ["model.c", "fmi3.c"], ["m"]⟩

def Recipe.xml (r : Recipe) : XML.Element :=
  ⟨"BuildConfiguration", [("modelIdentifier", r.identifier), ("platform", r.platform)],
    [⟨"SourceFileSet", [("language", r.language), ("compiler", r.compiler),
      ("compilerOptions", String.intercalate " " r.options)],
      r.sources.map (fun name => ⟨"SourceFile", [("name", name)], [], ""⟩), ""⟩] ++
    r.externalLibraries.map (fun name =>
      ⟨"Library", [("name", name), ("external", "true")], [], ""⟩), ""⟩

def description : XML.Element :=
  ⟨"fmiBuildDescription", [("fmiVersion", "3.0")],
    [ (recipe .x86_64Linux).xml, (recipe .aarch64Linux).xml ], ""⟩

structure Invocation where
  compiler : String
  args : List String
  deriving DecidableEq, Repr

/-- Paths are process arguments, never shell text. Link dependencies follow sources. -/
def invocation (p : Platform) (sources headers output : String) : Invocation :=
  let r := recipe p
  ⟨r.compiler, r.options ++ ["-fPIC", "-shared", "-I", headers] ++
    r.sources.map (fun file => sources ++ "/" ++ file) ++
    r.externalLibraries.map (fun lib => "-l" ++ lib) ++ ["-o", output]⟩

end Build
end Rumoca.FMI3
