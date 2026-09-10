import Rumoca.ArtifactCheck
import Rumoca.FMI3BuildProofs
import XML.CertificateCheck

register_option rumoca.fmi3.root : String :=
  { defValue := "", descr := "Prepared FMI 3 directory containing sources and source snapshot" }

namespace Rumoca.FMI3BuildArtifactCheck
open Lean Elab Command

/-- The fixed adapter independently reads all files and checks a fixed proposition.
The preliminary comparison only rejects; it is never proof authority. -/
elab "verify_fmi3_build_files" : command => do
  let directory := rumoca.fmi3.root.get (← getOptions)
  if directory.isEmpty then throwError "missing rumoca.fmi3.root"
  let root : System.FilePath := directory
  let source ← IO.FS.readFile (root / "extra/org.cognipilot.rumoca/Source.mo")
  let c ← IO.FS.readFile (root / "sources/model.c")
  let description ← IO.FS.readFile (root / "sources/buildDescription.xml")
  let grammar ← IO.FS.readFile "packages/modelica-parser/grammar/Modelica.ebnf"
  if description != XML.document FMI3.Build.description then
    throwError "actual FMI build description differs from the required source-build profile"
  ArtifactCheck.check source c grammar
  let tree := mkIdent `Rumoca.CheckedFMI3Files.build_tree
  let bytes := mkIdent `Rumoca.CheckedFMI3Files.build_bytes
  XML.CertificateCheck.certify tree.getId bytes.getId FMI3.Build.description description
  let treeEq := mkIdent `Rumoca.CheckedFMI3Files.build_tree_eq
  elabCommand (← `(command|
    theorem $treeEq:ident : FMI3.Build.description = $tree := by rfl))
  let src := Syntax.mkStrLit source
  let out := Syntax.mkStrLit c
  let xml := Syntax.mkStrLit description
  let ebnf := Syntax.mkStrLit grammar
  let numerical := mkIdent `Rumoca.CheckedFiles.source_to_c
  let theoremName := `Rumoca.CheckedFMI3Files.source_to_build
  let theoremId := mkIdent theoremName
  elabCommand (← `(command|
    theorem $theoremId:ident : Generated.source = $ebnf ∧ ∃ a : Artifact $src,
        compile $src = .ok a ∧ FMI3.SourceBuildContract a $out $xml := by
      obtain ⟨g, a, compiled, contract⟩ := $numerical:ident
      exact ⟨g, a, compiled, FMI3.sourceBuild_correct a $out $xml contract
        ((congrArg XML.document $treeEq:ident).trans $bytes:ident)⟩))
  let axioms ← collectAxioms theoremName
  for dependency in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
      throwError "unapproved axiom in FMI source-build contract: {dependency}"
  logInfo m!"{theoremName} depends on axioms: {axioms.toList}"

end Rumoca.FMI3BuildArtifactCheck
