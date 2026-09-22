import RumocaFMI3.PublicAPICertificate
import Rumoca.FMI3AdapterProofs
import RumocaC.PrinterCertificate
import Lean

/-! Kernel certificates for complete adapter bytes. Candidate signatures and
rendered chunks have no proof authority: each chunk is checked against its
function tree, and their concatenation against the independently read file.
The header collector is not claimed to implement the C header grammar. -/
namespace Rumoca.FMI3AdapterCertificate
open Lean Elab Command

open Rumoca.CTree.Printer.Certificate (quoteCharacters certifyConcatenation)

def quoteSignature (sig : CTree.Signature) : CommandElabM (TSyntax `term) := do
  let result := Syntax.mkStrLit sig.result
  let name := Syntax.mkStrLit sig.name
  let params ← sig.parameters.toArray.mapM fun p => do
    let type := Syntax.mkStrLit p.type
    let name := Syntax.mkStrLit p.name
    let array ← if p.array then `(term| true) else `(term| false)
    `(term| (⟨$type, $name, $array⟩ : CTree.Parameter))
  `(term| (⟨$result, $name, [$params,*]⟩ : CTree.Signature))

/-- Names of kernel-checked declarations, shared with the metadata checker. -/
structure Certificate where
  contract : Ident
  artifact : Ident
  compiled : Ident

/-- The kernel-checked identifiers a profile's `Contract` discharge consumes:
the target theorem name, the render-to-file equality, and the pinned signature
list in both quoted and native form. -/
structure ProfileCertContext where
  contract : Ident
  rendered : Ident
  signatures : Ident
  sigTerms : Array (TSyntax `term)
  witnessModel : TSyntax `term
  mTerm : TSyntax `term
  actualChars : Ident
  poolReady : Ident

/-- Everything a single adapter profile contributes to `certifyAdapterBytes`:
the synthetic scalar witness identity, the pinned model term, the native
render/function builders (which carry no proof authority), the identifiers of the
profile's function family and render-identity lemma, and the profile `Contract`
discharge closure. -/
structure ProfileCertInputs where
  witnessName : String
  witnessFile : String
  label : String
  base : Name
  mTerm : TSyntax `term
  renderActual : {source : AST.Model} → Solve.FMI3Model source → List CTree.Signature → String
  functionsOf : {source : AST.Model} → Solve.FMI3Model source → List CTree.Signature → List CTree.Function
  helpersCount : Nat
  helpersName : Name
  functionName : Name
  functionsName : Name
  renderName : Name
  adapterCharsLemma : Name
  preambleText : String
  preambleTerm : TSyntax `term
  dischargeContract : ProfileCertContext → CommandElabM Unit

/-- Certify each rendered adapter function against its native tree and rendered
bytes. `fnTerms` are the candidate function terms and `functions` their native
values, checked position by position; `label` only tags diagnostics. Returns the
per-function tree defs, tree equalities, character chunks, and byte equalities.
Native trees and rendered chunks have no proof authority: the tree equality is a
kernel `Eq.refl` and the bytes equality a `decide +kernel`, each restricted to the
three approved foundational axioms. -/
def certifyFunctions (base : Name) (label : String)
    (fnTerms : Array (TSyntax `term)) (functions : Array CTree.Function) :
    CommandElabM (Array Ident × Array Ident × Array Ident × Array Ident) := do
  let mut trees : Array Ident := #[]
  let mut treeEquations : Array Ident := #[]
  let mut chunks : Array Ident := #[]
  let mut equations : Array Ident := #[]
  for i in [:functions.size] do
    let fn := fnTerms[i]!
    let some function := functions[i]? | throwError "missing prepared {label}adapter function"
    let tree := mkIdent (base.str s!"function_{i}_tree")
    let quoted ← liftTermElabM <| PrettyPrinter.delab (toExpr function)
    elabCommand (← `(command| def $tree:ident : CTree.Function := $quoted))
    let treeEq := mkIdent (base.str s!"function_{i}_tree_eq")
    -- Ask Lean's kernel to check reflexivity directly. The elaborator's `rfl`
    -- reduction stops at string-pattern routing in some body branches. addDecl
    -- checks a theorem body; it does not create an axiom or trust the native tree
    -- value. This uses the same kernel path as `decide +kernel`.
    liftTermElabM do
      let type ← Term.elabType (← `(term| $fn = $tree))
      Term.synthesizeSyntheticMVarsNoPostponing
      let type ← instantiateMVars type
      let proof ← Meta.mkEqRefl (mkConst tree.getId)
      addDecl (.thmDecl { name := treeEq.getId, levelParams := [], type, value := proof })
    let treeAxioms ← collectAxioms treeEq.getId
    for dependency in treeAxioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "invalid {label}tree certificate for {function.signature.name}: {dependency}"
    let chars ← quoteCharacters (base.str s!"function_{i}") function.render
    let checked := mkIdent (base.str s!"function_{i}_bytes")
    -- Distribute characters over joins before kernel reduction. Evaluating a
    -- whole rendered String here creates much larger intermediate terms.
    elabCommand (← `(command|
      set_option linter.unusedSimpArgs false in
      theorem $checked:ident : ($fn).render.toList = $chars := by
        rw [$treeEq:ident]
        simp only [$tree:ident,
          CTree.Function.render, CTree.Signature.render, CTree.Parameter.render,
          CTree.Stmt.render, CTree.Expr.render, CTree.BinOp.render,
          List.map_cons, List.map_nil, CString.join_toList, String.toList_append,
          String.toList_ofList, List.flatMap_cons, List.flatMap_nil] <;>
          decide +kernel))
    let collected ← collectAxioms checked.getId
    for dependency in collected do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "invalid {label}printer certificate for {function.signature.name}: {dependency}"
    trees := trees.push tree
    treeEquations := treeEquations.push treeEq
    chunks := chunks.push chars
    equations := equations.push checked
  return (trees, treeEquations, chunks, equations)

/-- Shared certificate construction for a checked list of function trees. -/
def certifyReady (base : Name) (functions : TSyntax `term)
    (trees treeEquations : Array Ident) : CommandElabM Ident := do
  if trees.size != treeEquations.size then throwError "tree certificate length mismatch"
  let treesId := mkIdent (base.str "function_trees")
  elabCommand (← `(command| def $treesId:ident : List CTree.Function := [$trees,*]))
  let treesEq := mkIdent (base.str "function_trees_eq")
  let mut treeProof ← `(term| Eq.refl ([] : List CTree.Function))
  for i in [:treeEquations.size] do
    let equation := treeEquations[treeEquations.size - 1 - i]!
    treeProof ← `(term| congrArg₂ List.cons $equation $treeProof)
  elabCommand (← `(command| theorem $treesEq:ident : $functions = $treesId := $treeProof))
  let ready := mkIdent (base.str "literal_pool_ready")
  let treeUnfolds ← trees.mapM fun tree => `(Lean.Parser.Tactic.simpLemma| $tree:ident)
  elabCommand (← `(command| theorem $ready:ident :
      (CLiteral.Pool.forFunctions FMI3.LiteralPreparation.excluded $functions).isSome = true := by
    rw [$treesEq:ident]
    unfold CLiteral.Pool.forFunctions CLiteral.Pool.make CLiteral.Pool.check
    split
    · rfl
    · rename_i invalid
      apply False.elim
      apply invalid
      simp only [$treesId:ident, $treeUnfolds,*, CLiteral.PoolValid,
        CLiteral.functionNames, CLiteral.statementNames, CLiteral.Interface.names,
        CLiteral.functionTexts, CLiteral.statementTexts, CLiteral.expressionTexts,
        List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
        List.nil_append, List.cons_append, List.append_nil]
      decide +kernel))
  let dependencies ← collectAxioms ready.getId
  for dependency in dependencies do
    unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
      throwError "unapproved pool-readiness axiom: {dependency}"
  return ready

def certify (sourceFile source adapter : String) (sigs : List CTree.Signature)
    (actualChars : Ident) : CommandElabM Certificate := do
  let .ok candidate := compile (.single sourceFile source) | throwError "source compilation failed"
  let prepared := candidate.solve.prepareFMI3
  if FMI3.Runtime.render prepared sigs != adapter then
    throwError "actual FMI adapter differs from the complete prepared function list"
  let base := `Rumoca.CheckedFMI3Files.adapter
  let src := Syntax.mkStrLit source
  let file := Syntax.mkStrLit sourceFile
  let input ← `(term| Parser.Source.InputRef.single $file $src)
  let model := mkIdent (base.str "model")
  let parsed := mkIdent (base.str "parsed")
  let artifact := mkIdent (base.str "artifact")
  let compiled := mkIdent (base.str "compiled")
  let name := Syntax.mkStrLit candidate.parsed.ast.name
  let state := Syntax.mkStrLit candidate.parsed.ast.state
  let derivative := Syntax.mkStrLit candidate.parsed.ast.derivativeName
  let ending := Syntax.mkStrLit candidate.parsed.ast.endName
  elabCommand (← `(command| def $model:ident : AST.Model := ⟨$name, $state, $derivative, $ending⟩))
  elabCommand (← `(command| def $parsed:ident : Parsed $src :=
    ⟨($model).tokens, $model, by rfl, parseTokens_complete $model⟩))
  elabCommand (← `(command| def $artifact:ident : Artifact $input :=
    Artifact.ofParsed $input $parsed ⟨by decide +kernel, by decide +kernel⟩))
  elabCommand (← `(command| theorem $compiled:ident : compile $input = .ok $artifact :=
    compile_eq_parsed $input $parsed _))
  let sigTerms ← sigs.toArray.mapM quoteSignature
  let signatures := mkIdent (base.str "signatures")
  elabCommand (← `(command| def $signatures:ident : List CTree.Signature := [$sigTerms,*]))
  let ready := mkIdent (base.str "signatures_ready")
  elabCommand (← `(command| theorem $ready:ident :
    ∀ sig ∈ $signatures, @CCalls.Signature.Ready FMI3.cInterface sig := by
      change ∀ sig ∈ [$sigTerms,*], @CCalls.Signature.Ready FMI3.cInterface sig
      decide +kernel))
  let printable := mkIdent (base.str "signatures_printable")
  let signatureProof ← CTree.Printer.Certificate.signaturesProof
    (← `(term| FMI3.RuntimePrinter.typedefs)) sigs
  elabCommand (← `(command| set_option maxRecDepth 20000 in
    set_option maxHeartbeats 4000000 in
    theorem $printable:ident :
      ∀ sig ∈ $signatures, CTree.Printer.SignaturePrintable FMI3.RuntimePrinter.typedefs sig := $signatureProof))
  let m ← `(term| ($artifact).solve.prepareFMI3)
  let preamble ← `(term| FMI3.functionPrefix ($m).name ++ "#include \"model.c\"\n" ++ FMI3.Runtime.declarations)
  let preambleText := FMI3.functionPrefix prepared.name ++ "#include \"model.c\"\n" ++ FMI3.Runtime.declarations
  let preambleChars ← quoteCharacters (base.str "preamble") preambleText
  let preambleEq := mkIdent (base.str "preamble_bytes")
  elabCommand (← `(command| theorem $preambleEq:ident : ($preamble).toList = $preambleChars := by
    decide +kernel))
  let mut fnTerms : Array (TSyntax `term) := #[]
  for i in [:FMI3.Runtime.helpers.length] do
    let index := Syntax.mkNumLit (toString i)
    fnTerms := fnTerms.push (← `(term| FMI3.Runtime.helpers[$index]'(by decide +kernel)))
  for sig in sigTerms do
    fnTerms := fnTerms.push (← `(term| FMI3.Runtime.function $m $sig))
  let functions := (FMI3.LiteralPreparation.functions prepared sigs).toArray
  let (trees, treeEquations, chunks, equations) ← certifyFunctions base "" fnTerms functions
  let poolReady ← certifyReady base
    (← `(term| FMI3.LiteralPreparation.functions $m $signatures)) trees treeEquations
  let chunkList ← `(term| [$chunks,*])
  let matched := mkIdent (base.str "functions_matched")
  let mut pairProof ← `(term| List.Forall₂.nil)
  for i in [:equations.size] do
    let equation := equations[equations.size - 1 - i]!
    pairProof ← `(term| List.Forall₂.cons $equation $pairProof)
  elabCommand (← `(command| theorem $matched:ident :
    List.Forall₂ (fun fn chars => fn.render.toList = chars)
      (FMI3.LiteralPreparation.functions $m $signatures) $chunkList := $pairProof))
  let completeBytes := mkIdent (base.str "complete_bytes")
  let concatenated ← certifyConcatenation (base.str "assembly") actualChars
    (#[preambleChars] ++ chunks)
    (#[preambleText.toList.length] ++ functions.map (fun fn => fn.render.toList.length))
  elabCommand (← `(command| theorem $completeBytes:ident :
    $preambleChars ++ ($chunkList).flatten = $actualChars := $concatenated))
  let rendered := mkIdent (base.str "rendered")
  elabCommand (← `(command| theorem $rendered:ident :
    FMI3.Runtime.render $m $signatures = String.ofList $actualChars :=
      FMI3.adapter_chars $m $signatures $preambleChars $chunkList $actualChars
        $preambleEq $matched $completeBytes))
  let theoremId := mkIdent (base.str "contract")
  elabCommand (← `(command| theorem $theoremId:ident (a : Artifact $input)
    (accepted : compile $input = .ok a) : FMI3.AdapterContract a (String.ofList $actualChars) := by
      have same : a = $artifact := Except.ok.inj (accepted.symm.trans $compiled)
      subst a
      apply FMI3.adapter_correct $artifact $signatures
      · decide +kernel
      · change FMI3.Reset.signature ∈ [$sigTerms,*]
        simp [FMI3.Reset.signature]
      · change ∀ sig ∈ [$sigTerms,*], CTree.Preprocessing.SignatureInputs sig
        decide +kernel
      · exact $printable
      · exact $ready
      · intro events
        cases events <;> change FMI3.CountQueries.signature _ ∈ [$sigTerms,*]
        all_goals simp [FMI3.CountQueries.signature, FMI3.CountQueries.outputName]
      · change FMI3.Version.signature ∈ [$sigTerms,*]
        simp [FMI3.Version.signature]
      · change FMI3.ErrorCalls.nominalSignature ∈ [$sigTerms,*]
        simp [FMI3.ErrorCalls.nominalSignature]
      · intro write
        cases write <;> change FMI3.StateCalls.signature _ ∈ [$sigTerms,*]
        all_goals simp [FMI3.StateCalls.signature]
      · change FMI3.DerivativeCalls.signature ∈ [$sigTerms,*]
        simp [FMI3.DerivativeCalls.signature]
      · change FMI3.Float64Calls.signature false ∈ [$sigTerms,*]
        simp [FMI3.Float64Calls.signature]
      · change FMI3.Float64Calls.signature true ∈ [$sigTerms,*]
        simp [FMI3.Float64Calls.signature]
      · change FMI3.InitializationCalls.signature ∈ [$sigTerms,*]
        simp [FMI3.InitializationCalls.signature]
      · change FMI3.InitializationExit.signature ∈ [$sigTerms,*]
        simp [FMI3.InitializationExit.signature]
      · change ∀ sig ∈ [$sigTerms,*], ∀ function,
          sig.name ≠ FMI3.LiteralPreparation.kernelName function
        intro sig member function
        cases function
        all_goals revert sig
        all_goals decide +kernel
      · change ∀ sig ∈ [$sigTerms,*], sig.name ∉ CStringCalls.routineNames
        decide +kernel
      · intro kind
        cases kind <;> change FMI3.FactoryArguments.signature _ ∈ [$sigTerms,*]
        all_goals simp [FMI3.FactoryArguments.signature, FMI3.Identity.factoryName]
      · change FMI3.StaticRelease.function.signature ∈ [$sigTerms,*]
        simp [FMI3.StaticRelease.function]
      · change ∀ sig ∈ [$sigTerms,*], sig.name ∉ FMI3.StaticRuntime.routineNames
        decide +kernel
      · change FMI3.Termination.signature ∈ [$sigTerms,*]
        simp [FMI3.Termination.signature]
      · change FMI3.TimeCalls.signature ∈ [$sigTerms,*]
        simp [FMI3.TimeCalls.signature]
      · intro entry
        cases entry <;> change FMI3.EventEntry.signature _ ∈ [$sigTerms,*]
        all_goals simp [FMI3.EventEntry.signature]
      · change FMI3.CompletedCalls.signature ∈ [$sigTerms,*]
        simp [FMI3.CompletedCalls.signature]
      · change FMI3.DiscreteCalls.signature ∈ [$sigTerms,*]
        simp [FMI3.DiscreteCalls.signature]
      · change FMI3.StepEntry.signature ∈ [$sigTerms,*]
        simp [FMI3.StepEntry.signature]
      · change FMI3.DebugLogging.signature ∈ [$sigTerms,*]
        simp [FMI3.DebugLogging.signature]
      · change FMI3.EventIndicatorCalls.signature ∈ [$sigTerms,*]
        simp [FMI3.EventIndicatorCalls.signature]
      · change FMI3.DiscreteEvaluation.signature ∈ [$sigTerms,*]
        simp [FMI3.DiscreteEvaluation.signature]
      · intro ty write
        cases ty <;> cases write <;> change FMI3.AbsentVariables.signature _ _ ∈ [$sigTerms,*]
        all_goals simp [FMI3.AbsentVariables.signature, FMI3.AbsentVariables.VariableType.name,
          FMI3.AbsentVariables.VariableType.hasSizes]
      · change ∀ sig ∈ FMI3.CapabilityRejection.signatures, sig ∈ [$sigTerms,*]
        simp [FMI3.CapabilityRejection.signatures]
      · change FMI3.ScheduledCreation.signature ∈ [$sigTerms,*]
        simp [FMI3.ScheduledCreation.signature]
      · change FMI3.PublicAPI.Covered [$sigTerms,*]
        fmi_public_coverage
      · exact $poolReady
      · exact $rendered))
  return ⟨theoremId, artifact, compiled⟩

/-- The render-contract adapter-bytes certificate shared by the tensor and
constant profiles: build the scalar witness artifact, certify every emitted
function against its tree and rendered bytes, join the chunks and bind them to
the independently read file, prove the profile render equals that file, and hand
the profile `Contract` discharge the assembled context. Candidate signatures,
native trees and rendered chunks carry no proof authority; each is checked by the
kernel against the reachable definition. Returns the profile `Contract` proof
identifier and the reconstructed scalar witness artifact identifier. -/
def certifyAdapterBytes (inp : ProfileCertInputs) (adapter : String)
    (sigs : List CTree.Signature) (actualChars : Ident) :
    CommandElabM (Ident × Ident) := do
  let scalarSource :=
    "model " ++ inp.witnessName ++ " Real x; equation der(x) = 1; end " ++ inp.witnessName ++ ";"
  let .ok witness := compile (.single inp.witnessFile scalarSource)
    | throwError "scalar witness compilation failed"
  let witnessModelVal := witness.solve.prepareFMI3
  if inp.renderActual witnessModelVal sigs != adapter then
    throwError "actual {inp.label}FMI adapter differs from the complete prepared function list"
  let base := inp.base
  let src := Syntax.mkStrLit scalarSource
  let file := Syntax.mkStrLit inp.witnessFile
  let input ← `(term| Parser.Source.InputRef.single $file $src)
  let model := mkIdent (base.str "model")
  let parsed := mkIdent (base.str "parsed")
  let artifact := mkIdent (base.str "artifact")
  let compiled := mkIdent (base.str "compiled")
  let name := Syntax.mkStrLit witness.parsed.ast.name
  let state := Syntax.mkStrLit witness.parsed.ast.state
  let derivative := Syntax.mkStrLit witness.parsed.ast.derivativeName
  let ending := Syntax.mkStrLit witness.parsed.ast.endName
  elabCommand (← `(command| def $model:ident : AST.Model := ⟨$name, $state, $derivative, $ending⟩))
  elabCommand (← `(command| def $parsed:ident : Parsed $src :=
    ⟨($model).tokens, $model, by rfl, parseTokens_complete $model⟩))
  elabCommand (← `(command| def $artifact:ident : Artifact $input :=
    Artifact.ofParsed $input $parsed ⟨by decide +kernel, by decide +kernel⟩))
  elabCommand (← `(command| theorem $compiled:ident : compile $input = .ok $artifact :=
    compile_eq_parsed $input $parsed _))
  let witnessModel ← `(term| ($artifact).solve.prepareFMI3)
  let mTerm := inp.mTerm
  let sigTerms ← sigs.toArray.mapM quoteSignature
  let signatures := mkIdent (base.str "signatures")
  elabCommand (← `(command| def $signatures:ident : List CTree.Signature := [$sigTerms,*]))
  let functions := (inp.functionsOf witnessModelVal sigs).toArray
  let helpers := mkIdent inp.helpersName
  let functionCtor := mkIdent inp.functionName
  let mut fnTerms : Array (TSyntax `term) := #[]
  for i in [:inp.helpersCount] do
    let index := Syntax.mkNumLit (toString i)
    fnTerms := fnTerms.push (← `(term| ($helpers)[$index]'(by decide +kernel)))
  for sig in sigTerms do
    fnTerms := fnTerms.push (← `(term| $functionCtor $witnessModel $mTerm $sig))
  let (trees, treeEquations, chunks, equations) ← certifyFunctions base inp.label fnTerms functions
  let functionsId := mkIdent inp.functionsName
  let poolReady ← certifyReady base
    (← `(term| $functionsId $witnessModel $mTerm $signatures)) trees treeEquations
  let chunkList ← `(term| [$chunks,*])
  let matched := mkIdent (base.str "functions_matched")
  let mut pairProof ← `(term| List.Forall₂.nil)
  for i in [:equations.size] do
    let equation := equations[equations.size - 1 - i]!
    pairProof ← `(term| List.Forall₂.cons $equation $pairProof)
  elabCommand (← `(command| theorem $matched:ident :
    List.Forall₂ (fun fn chars => fn.render.toList = chars)
      ($functionsId $witnessModel $mTerm $signatures) $chunkList := $pairProof))
  let preambleChars ← quoteCharacters (base.str "preamble") inp.preambleText
  let preambleEq := mkIdent (base.str "preamble_bytes")
  let preambleTerm := inp.preambleTerm
  elabCommand (← `(command| theorem $preambleEq:ident :
    ($preambleTerm).toList = $preambleChars := by decide +kernel))
  let concatenated ← certifyConcatenation (base.str "assembly") actualChars
    (#[preambleChars] ++ chunks)
    (#[inp.preambleText.toList.length] ++ functions.map (fun fn => fn.render.toList.length))
  let completeBytes := mkIdent (base.str "complete_bytes")
  elabCommand (← `(command| theorem $completeBytes:ident :
    $preambleChars ++ ($chunkList).flatten = $actualChars := $concatenated))
  let renderId := mkIdent inp.renderName
  let adapterCharsId := mkIdent inp.adapterCharsLemma
  let rendered := mkIdent (base.str "rendered")
  elabCommand (← `(command| theorem $rendered:ident :
    $renderId $witnessModel $mTerm $signatures = String.ofList $actualChars :=
      $adapterCharsId $witnessModel $mTerm $signatures
        $preambleChars $chunkList $actualChars $preambleEq $matched $completeBytes))
  let contract := mkIdent (base.str "contract")
  inp.dischargeContract {
    contract, rendered, signatures, sigTerms, witnessModel, mTerm, actualChars, poolReady }
  return (contract, artifact)

end Rumoca.FMI3AdapterCertificate
