import Rumoca.ArtifactCheck
import Rumoca.FMI3BuildProofs
import XML.CertificateCheck

register_option rumoca.fmi3.root : String :=
  { defValue := "", descr := "Prepared FMI 3 directory containing sources and source snapshot" }

namespace Rumoca.FMI3BuildArtifactCheck
open Lean Elab Command

/-- Quote every independently read character, in bounded blocks. This is an
input representation, not producer-supplied proof data: the final proposition
uses `String.ofList` of precisely these characters. No native prefix comparison
can establish its required decomposition. -/
private def quoteCharacters (name : Name) (input : String) : CommandElabM Ident := do
  let chars := input.toList.toArray
  let count := (chars.size + 255) / 256
  let part := fun i => mkIdent (name.str s!"part_{i}")
  let last := part count
  elabCommand (← `(command| def $last:ident : List Char := []))
  for j in [:count] do
    let i := count - 1 - j
    let values ← (chars.toSubarray (i * 256) (min ((i + 1) * 256) chars.size)).toArray.mapM fun c => do
      let n := Syntax.mkNumLit (toString c.toNat)
      `(term| Char.ofNat $n)
    let current := part i
    let rest := part (i + 1)
    elabCommand (← `(command| def $current:ident : List Char := [$values,*] ++ $rest))
  return part 0

/-- The fixed adapter independently reads all files and checks a fixed proposition.
Preliminary comparisons only reject; candidate data is never proof authority. -/
elab "verify_fmi3_build_files" : command => do
  let directory := rumoca.fmi3.root.get (← getOptions)
  if directory.isEmpty then throwError "missing rumoca.fmi3.root"
  let root : System.FilePath := directory
  let sourcePath := root / "extra/org.cognipilot.rumoca/Source.mo"
  let source ← IO.FS.readFile sourcePath
  let c ← IO.FS.readFile (root / "sources/model.c")
  let adapter ← IO.FS.readFile (root / "sources/fmi3.c")
  let description ← IO.FS.readFile (root / "sources/buildDescription.xml")
  let metadata ← IO.FS.readFile (root / "modelDescription.xml")
  let grammar ← IO.FS.readFile "packages/modelica-parser/grammar/Modelica.ebnf"
  let .ok candidate := compile (.single sourcePath.toString source) | throwError "source compilation failed"
  let modelName := candidate.parsed.ast.name
  let buildTree := FMI3.Build.description modelName
  let metadataTree := FMI3.modelDescription candidate.solve.prepareFMI3
  let expectedPrefix := FMI3.functionPrefix modelName ++ "#include \"model.c\"\n"
  if description != XML.document buildTree then
    throwError "actual FMI build description differs from the required source-build profile"
  if metadata != XML.document metadataTree then
    throwError "actual FMI model description differs from the prepared model"
  if !adapter.startsWith expectedPrefix then
    throwError "actual FMI source prefix or private-kernel inclusion differs from its model identifier"
  ArtifactCheck.check sourcePath.toString source c grammar .internal
  let tree := mkIdent `Rumoca.CheckedFMI3Files.build_tree
  let bytes := mkIdent `Rumoca.CheckedFMI3Files.build_bytes
  XML.CertificateCheck.certify tree.getId bytes.getId buildTree description
  let name := Syntax.mkStrLit modelName
  let treeEq := mkIdent `Rumoca.CheckedFMI3Files.build_tree_eq
  elabCommand (← `(command|
    theorem $treeEq:ident : FMI3.Build.description $name = $tree := by rfl))
  let mdTree := mkIdent `Rumoca.CheckedFMI3Files.metadata_tree
  let mdBytes := mkIdent `Rumoca.CheckedFMI3Files.metadata_bytes
  XML.CertificateCheck.certify mdTree.getId mdBytes.getId metadataTree metadata
  XML.CertificateCheck.certifyValidity mdTree.getId metadataTree
  let mdValid := mkIdent (mdTree.getId.str "valid_eq")
  let identifiers := mkIdent `Rumoca.CheckedFMI3Files.model_identifiers
  elabCommand (← `(command|
    theorem $identifiers:ident : FMI3.decodeModelIdentifiers $mdTree =
        some ($name, FMI3.modelIdentifier $name, FMI3.modelIdentifier $name) := by decide +kernel))
  let src := Syntax.mkStrLit source
  let sourceFile := Syntax.mkStrLit sourcePath.toString
  let inputTerm ← `(term| Parser.Source.InputRef.single $sourceFile $src)
  let out := Syntax.mkStrLit c
  let xml := Syntax.mkStrLit description
  let md := Syntax.mkStrLit metadata
  let chars ← quoteCharacters `Rumoca.CheckedFMI3Files.adapter_chars adapter
  let api ← `(term| String.ofList $chars)
  let prefixBytes := mkIdent `Rumoca.CheckedFMI3Files.source_prefix_bytes
  elabCommand (← `(command|
    theorem $prefixBytes:ident : ("#define FMI3_FUNCTION_PREFIX " ++ FMI3.modelIdentifier $name ++
        "_\n" ++ "#include \"model.c\"\n").toList <+: $chars := by decide +kernel))
  let ebnf := Syntax.mkStrLit grammar
  let numerical := mkIdent `Rumoca.CheckedFiles.source_to_c
  let sourceName := mkIdent `Rumoca.CheckedFiles.source_model_name
  let theoremName := `Rumoca.CheckedFMI3Files.source_to_build
  let theoremId := mkIdent theoremName
  elabCommand (← `(command|
    theorem $theoremId:ident : Generated.source = $ebnf ∧ ∃ a : Artifact $inputTerm,
        compile $inputTerm = .ok a ∧ FMI3.SourceBuildContract a $out $xml $api $md := by
      obtain ⟨g, a, compiled, contract⟩ := $numerical:ident
      have hn := $sourceName:ident a.parsed
      refine ⟨g, a, compiled, FMI3.sourceBuild_correct a $out $xml $api $md contract ?_ ?_ ?_⟩
      · rw [hn]
        exact (congrArg XML.document $treeEq:ident).trans $bytes:ident
      · apply FMI3.sourcePrefix_of_chars _ _ (FMI3.parsed_functionPrefix a.parsed)
        rw [hn]
        exact $prefixBytes:ident
      · refine ⟨$mdTree, ?_, ?_⟩
        · rw [← $mdBytes:ident]
          exact XML.document_correct $mdTree $mdValid:ident
        · rw [hn]
          exact $identifiers:ident))
  let axioms ← collectAxioms theoremName
  for dependency in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
      throwError "unapproved axiom in FMI source-build contract: {dependency}"
  logInfo m!"{theoremName} depends on axioms: {axioms.toList}"

end Rumoca.FMI3BuildArtifactCheck
