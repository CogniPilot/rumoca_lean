import Rumoca.Compiler
import Parser.LALR.EBNF
import ModelicaParser.Driven
import Rumoca.ArrayCompiler
import Rumoca.ConstantCompiler
import RumocaCore.Solve.IVP
import RumocaCore.Solve.Tensor.Reverse
import Rumoca.EFMIIdentity
import RumocaFMI3.TensorMetadata
import RumocaFMI3.TensorInstanceRhs
import RumocaFMI3.BuildDescription
import RumocaFMI3.Header
import Tests.TensorMetadataFixture
import Tests.TensorAdapterFixture
import Tests.ConstantAdapterFixture
import RumocaCore.Solve.ConstantFMI3
import RumocaFMI3.ConstantFunctions
import Rumoca.EFMITensorAlgorithm
import Rumoca.EFMITensorProduction

open _root_.Parser

open Rumoca

def expect (label : String) (condition : Bool) : IO Unit :=
  if condition then pure () else throw (IO.userError s!"FAIL: {label}")

def accepted (s : String) : Bool := match compile (.single "rumoca-check:/compiler/model.mo" s) with
  | .ok _ => true
  | .error _ => false

def grammarLowered (s : String) : Bool := match LALR.Frontend.compile s with
  | .ok _ => true
  | .error _ => false

def drivenAccepted (s : String) : Bool := match Driven.parse s with
  | .error _ => false
  | .ok parsed => match Driven.resolve parsed.ast with
    | .error _ => false
    | .ok _ => true

def main : IO Unit := do
  let good := "model Integrator Real x; equation der(x) = 1; end Integrator;"
  expect "minimal model" (accepted good)
  let driven := "model Driven input Real u; output Real x(start=0, fixed=true); equation der(x)=u; end Driven;"
  expect "driven parser and resolution" (drivenAccepted driven)
  expect "driven profile not prematurely admitted by C compiler" (!accepted driven)
  let arrayDriven ← IO.FS.readFile "examples/development/ArrayDriven.mo"
  let arraySquare ← IO.FS.readFile "examples/development/TensorSquare.mo"
  for source in [arrayDriven, arraySquare] do
    match ArrayCompiler.prepare source with
    | .error e => throw (IO.userError s!"array frontend: {e.message}")
    | .ok prepared =>
      let p := prepared.parsed
      let kernel := prepared.kernel
      let state := Tensor.Value.fill ArrayProfile.stateShape 7
      let input : Tensor.Value Nat ArrayProfile.stateShape := ⟨Vector.ofFn (fun i => i.val + 2)⟩
      let ops : Tensor.ScalarOps Nat := ⟨Nat.add, Nat.mul, Nat.sub, Nat.div, id⟩
      expect "array fixed initialization and state observation"
        (kernel.problem.initial ops 0 1 == Tensor.Value.fill ArrayProfile.stateShape 0 &&
          kernel.problem.outputs ops 0 1 state input == state)
      match p.parsed.ast.body, kernel.diagonal with
      | .driven .., none =>
        expect "parsed driven array reaches executable Solve IR" (kernel.problem.rhs ops 0 1 state input == input)
      | .jacobian .., some matrix =>
        expect "parsed square and Jacobian reach executable Solve IR"
          ((kernel.problem.rhs ops 0 1 state input).data.toArray == #[4, 9] &&
            (matrix.eval ops 0 1 (kernel.problem.environment state input)).data.toArray == #[4, 0, 0, 6])
        -- Development tensor eFMI Algorithm Code product. The array/tensor
        -- profile is not admitted to CLI eFMI output; this renders the actual
        -- GALEC text for the prepared square kernel and checks it parses to the
        -- resolved tensor block, the boundary the Lean product proves.
        let algorithmSource := EFMI.renderTensorAlgorithm
          (⟨EFMI.squareKernel ArrayProfile.stateShape, rfl⟩ : EFMI.TensorModel ArrayProfile.stateShape)
        match GALEC.Syntax.parseTensor algorithmSource with
        | .error e => throw (IO.userError s!"tensor Algorithm Code rejected: {e}")
        | .ok algParsed =>
          expect "tensor Algorithm Code parses to the resolved tensor square block"
            (algParsed.ast == GALEC.Syntax.tensorUnit)
        IO.FS.createDirAll "build/tensor-efmi"
        IO.FS.writeFile "build/tensor-efmi/AlgorithmCode.alg" algorithmSource
        -- Development tensor eFMI Production Code and manifest product. The
        -- array/tensor profile is not admitted to CLI eFMI output; this renders
        -- the certified-kernel Production translation unit and the Algorithm/
        -- Production/container manifests for the prepared square kernel and
        -- retains them under build/tensor-efmi/ for the boundary XSD check.
        let tensorIdentity := EFMIIdentity.derivedIdentity "TensorSquare" arraySquare 1700000000
        let tensorDocs := EFMI.TensorManifest.prepare "TensorSquare" tensorIdentity algorithmSource
        expect "tensor eFMI manifests lie in the checked XML output profile"
          tensorDocs.valid
        IO.FS.writeFile "build/tensor-efmi/ProductionCode.c" EFMI.TensorProduction.render
        IO.FS.writeFile "build/tensor-efmi/AlgorithmCode.xml" (XML.document tensorDocs.algorithm)
        IO.FS.writeFile "build/tensor-efmi/ProductionCode.xml" (XML.document tensorDocs.production)
        IO.FS.writeFile "build/tensor-efmi/content.xml" (XML.document tensorDocs.content)
        let preparedModel : Solve.TensorFMI3Model ArrayProfile.stateShape := ⟨"TensorSquare", kernel⟩
        expect "prepared TensorSquare renders the fixture's well-formed tensor model description"
          (preparedModel.hasOutput &&
            (FMI3.TensorMetadata.modelDescription preparedModel).valid &&
            XML.document (FMI3.TensorMetadata.modelDescription preparedModel)
              == XML.document (FMI3.TensorMetadata.modelDescription
                  Tests.TensorMetadataFixture.fixtureModel))
        expect "prepared TensorSquare RHS matches the tensor instance record's bound derivative"
          (kernel.problem.rhs ops 0 1 state input ==
            (FMI3.TensorInstanceRhs.kernel ArrayProfile.stateShape).problem.rhs ops 0 1 state input)
        expect "prepared TensorSquare renders the fixture's tensor adapter bytes"
          (FMI3.TensorFunctions.render Tests.TensorAdapterFixture.scalarModel preparedModel
              Tests.TensorAdapterFixture.signatures
            == Tests.TensorAdapterFixture.adapterBytes)
        -- Full pinned header signature list: obtain the 75 signatures the way the
        -- scalar path does, from the vendored fmi3FunctionTypes.h, render the
        -- complete tensor adapter for the actual prepared kernel and retain it.
        let header ← IO.FS.readFile "packages/backend-fmi3/vendor/fmi3/fmi3FunctionTypes.h"
        match FMI3.Header.signatures header with
        | .error e => throw (IO.userError s!"FMI header signatures: {e}")
        | .ok fullSignatures =>
          let full := FMI3.TensorFunctions.render Tests.TensorAdapterFixture.scalarModel
            preparedModel fullSignatures
          expect "full pinned header signature list has the expected count"
            (fullSignatures.length == 75)
          -- The whole rendered text is the fixed preamble (model prefix, private
          -- kernel inclusion and the tensor declaration block with the kernel
          -- prototype) followed by the tensor function list, one function per
          -- reused helper and per pinned signature. This is the concrete instance
          -- of `TensorFunctions.rendered_functions`, whose function section is
          -- certified against the maximal-munch grammar by
          -- `TensorAdapterPrinter.rendered_contract`.
          expect "full tensor adapter is the fixed preamble followed by the tensor function list"
            (full == FMI3.functionPrefix preparedModel.name ++ "#include \"model.c\"\n" ++
                FMI3.TensorStorage.declarations ArrayProfile.stateShape preparedModel.hasOutput ++
                String.join ((FMI3.TensorFunctions.functions Tests.TensorAdapterFixture.scalarModel
                    preparedModel fullSignatures).map CTree.Function.render))
          expect "the full tensor function list has one function per reused helper and pinned signature"
            ((FMI3.TensorFunctions.functions Tests.TensorAdapterFixture.scalarModel
                preparedModel fullSignatures).length == FMI3.TensorFunctions.helpers.length + 75)
          IO.FS.createDirAll "build/tensor-fmi"
          IO.FS.writeFile "build/tensor-fmi/adapter.c" full
          -- Retain the checked model description and a build description mirroring
          -- the scalar recipe, for the development tensor FMU the boundary script
          -- assembles. These are development artifacts, not a production FMU.
          IO.FS.writeFile "build/tensor-fmi/modelDescription.xml"
            (XML.document (FMI3.TensorMetadata.modelDescription preparedModel))
          IO.FS.writeFile "build/tensor-fmi/buildDescription.xml"
            (XML.document (FMI3.Build.description preparedModel.name))
      | _, _ => throw (IO.userError "Solve observation does not match the source profile")
      match ArrayProfile.LocatedParsed.call? p with
      | none => pure ()
      | some ⟨call, locations⟩ =>
        expect "ordinary call retains builtin name and argument source ranges"
          (call.name == "jacobian" && locations.name.text == "jacobian" &&
            locations.expressionSpan.text == "u .* u" && locations.wrt.text == "u" &&
            locations.span.text == "jacobian (u .* u, u)")
    expect "array profile requires a target contract before compilation" (!accepted source)
  match ArrayProfile.parseLocated (arraySquare.replace "jacobian" "other") with
  | .error e => throw (IO.userError s!"ordinary function call did not parse: {e.message}")
  | .ok p => match ArrayProfile.LocatedParsed.resolve p with
    | .ok _ => throw (IO.userError "unrecognized builtin was resolved")
    | .error e => expect "unknown function diagnosed at its own source range" (e.span.text == "other")
  -- G01 constant-rate development profile: two states with signed decimal rates.
  let constantRates ← IO.FS.readFile "examples/ConstantRates.mo"
  expect "constant-rate profile not admitted by the production C compiler" (!accepted constantRates)
  match ConstantCompiler.prepare constantRates with
  | .error e => throw (IO.userError s!"constant frontend: {e.message}")
  | .ok prepared =>
    let ast := prepared.parsed.parsed.ast
    expect "constant frontend recovers two declared states" (ast.states == ["x", "y"])
    expect "constant frontend recovers each der reference"
      (ast.equations.map (·.derivative) == ["x", "y"])
    expect "constant frontend recovers the signed decimal rate spellings"
      (ast.equations.map (·.rate) == ["2.5", "-1"])
    expect "prepared literal content of the fraction rate"
      (decide (ast.decimalOf "x" = ⟨1, 25, -1⟩))
    expect "prepared literal content of the signed integer rate"
      (decide (ast.decimalOf "y" = ⟨-1, 1, 0⟩))
    -- Render the constant-rate FMI 3 adapter for the actual prepared kernel and
    -- retain it under build/constant-fmi/. The prepared multi-state IVP is the
    -- constant model kernel witness; the model-independent bodies reuse the scalar
    -- witness. This ties the actual ConstantCompiler.prepare rates to the
    -- ConstantAdapterFixture rendering the function-section grammar check certifies.
    let preparedConstantModel : Solve.ConstantFMI3Model ast.states.length :=
      ⟨"ConstantRates", prepared.ivp⟩
    expect "prepared ConstantRates renders the fixture's constant adapter bytes"
      (FMI3.ConstantFunctions.render Tests.ConstantAdapterFixture.scalarModel preparedConstantModel
          Tests.ConstantAdapterFixture.signatures
        == Tests.ConstantAdapterFixture.adapterBytes)
    let header ← IO.FS.readFile "packages/backend-fmi3/vendor/fmi3/fmi3FunctionTypes.h"
    match FMI3.Header.signatures header with
    | .error e => throw (IO.userError s!"FMI header signatures: {e}")
    | .ok fullSignatures =>
      let full := FMI3.ConstantFunctions.render Tests.ConstantAdapterFixture.scalarModel
        preparedConstantModel fullSignatures
      expect "full pinned header signature list has the expected count"
        (fullSignatures.length == 75)
      -- The whole rendered text is the fixed preamble (model prefix, private kernel
      -- inclusion and the constant declaration block with the three constant kernel
      -- prototypes) followed by the constant function list, one function per reused
      -- helper and per pinned signature. This is the concrete instance of
      -- `ConstantFunctions.rendered_functions`, whose function section is certified
      -- against the maximal-munch grammar by `ConstantAdapterPrinter.rendered_contract`.
      expect "full constant adapter is the fixed preamble followed by the constant function list"
        (full == FMI3.functionPrefix preparedConstantModel.name ++ "#include \"model.c\"\n" ++
            FMI3.ConstantFunctions.declarations preparedConstantModel.shape
              (FMI3.ConstantFunctions.rates preparedConstantModel) ++
            String.join ((FMI3.ConstantFunctions.functions Tests.ConstantAdapterFixture.scalarModel
                preparedConstantModel fullSignatures).map CTree.Function.render))
      expect "the full constant function list has one function per reused helper and pinned signature"
        ((FMI3.ConstantFunctions.functions Tests.ConstantAdapterFixture.scalarModel
            preparedConstantModel fullSignatures).length == FMI3.ConstantFunctions.helpers.length + 75)
      IO.FS.createDirAll "build/constant-fmi"
      IO.FS.writeFile "build/constant-fmi/adapter.c" full
  -- Reordering the two equations must not change the recovered rates.
  match ConstantCompiler.prepare (constantRates.replace "der(x) = 2.5;\n  der(y) = -1;"
      "der(y) = -1;\n  der(x) = 2.5;") with
  | .error e => throw (IO.userError s!"reordered constant frontend: {e.message}")
  | .ok reordered =>
    expect "reordered constant equations keep the declared state order"
      (reordered.parsed.parsed.ast.states == ["x", "y"])
    expect "reordered constant equations keep each state's rate"
      (reordered.parsed.parsed.ast.equations.map (·.derivative) == ["y", "x"])
  -- Malformed and unresolved constant sources are rejected by the frontend.
  for bad in [constantRates.replace "der(y) = -1" "der(z) = -1",
      constantRates.replace "Real y;" "Real x;",
      constantRates.replace "end ConstantRates" "end Other",
      constantRates.replace "= 2.5" "= notanumber"] do
    match ConstantCompiler.prepare bad with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "constant frontend admitted an unresolved source")
  expect "attribute names are identifiers" (drivenAccepted
    "model M input Real fixed; output Real start(start=0, fixed=true); equation der(start)=fixed; end M;")
  for bad in [driven.replace "der(x)" "der(u)", driven.replace "=u;" "=x;",
      driven.replace "start=0" "wrong=0", driven.replace "fixed=true" "wrong=true",
      driven.replace "input Real u" "input Real x", driven.replace "end Driven" "end Other",
      driven.replace "start=0" "start=1", driven.replace "fixed=true" "fixed=false"] do
    expect "driven reference/initialization rejection" (!drivenAccepted bad)
  let shape : Tensor.Shape := ⟨[2, 3]⟩
  let input : Tensor.Value Nat shape := ⟨Vector.ofFn (fun i : Fin 6 => i.val + 1)⟩
  let state := Tensor.Value.fill shape 9
  expect "tensor derivative preserves every input element"
    ((Solve.drivenIVP shape).rhs ⟨Nat.add, Nat.mul, Nat.sub, Nat.div, id⟩ 0 1 state input == input)
  expect "tensor output preserves the state"
    ((Solve.drivenIVP shape).outputs ⟨Nat.add, Nat.mul, Nat.sub, Nat.div, id⟩ 0 1 state input == state)
  expect "tensor initialization fills the state"
    ((Solve.drivenIVP shape).initial ⟨Nat.add, Nat.mul, Nat.sub, Nat.div, id⟩ (0 : Nat) 1 == Tensor.Value.fill shape 0)
  -- One native boundary check for shared nonlinear intermediates: (u .* u + 1)^2.
  let program : Solve.Tensor.Program [shape] shape :=
    .binary .mul .here .here (.fill shape .one
      (.binary .add (.there .here) .here (.binary .mul .here .here (.ret .here))))
  let primal : Solve.Tensor.Ren [shape] [shape, shape] :=
    Solve.Tensor.Ren.push .here Solve.Tensor.Ren.empty
  let tangent : Solve.Tensor.Ren [shape] [shape, shape] :=
    Solve.Tensor.Ren.push (.there .here) Solve.Tensor.Ren.empty
  let ones := Tensor.Value.fill shape 1
  let values : Solve.Tensor.Env Nat [shape] := Solve.Tensor.Env.push input Solve.Tensor.Env.empty
  let duals : Solve.Tensor.Env Nat [shape, shape] :=
    Solve.Tensor.Env.push input (Solve.Tensor.Env.push ones Solve.Tensor.Env.empty)
  let reverse := program.reverse ⟨Nat.add, Nat.mul, Nat.sub, Nat.div, id⟩ 0 1 values
  let expected : Tensor.Value Nat shape := ⟨input.data.map (fun x => (x * x + 1) * (x * x + 1))⟩
  let expectedDerivative : Tensor.Value Nat shape := ⟨input.data.map (fun x => 4 * x * (x * x + 1))⟩
  expect "native tensor program AD shares intermediates and accumulates both operand uses"
    (reverse.value == expected &&
      (program.forward primal tangent .primal).eval ⟨Nat.add, Nat.mul, Nat.sub, Nat.div, id⟩ 0 1 duals == expected &&
      (program.forward primal tangent .tangent).eval ⟨Nat.add, Nat.mul, Nat.sub, Nat.div, id⟩ 0 1 duals == expectedDerivative &&
      reverse.pullback ones .here == expectedDerivative)
  expect "identifiers and whitespace" (accepted
    "\r\nmodel _M2\tReal x2; equation der (x2)=1; end _M2;\n")
  for bad in ["", "der(x) = 1;", good ++ "garbage", good ++ ";",
      "model M Real x; equation der(x)=2; end M;",
      "model M Real x; equation der(y)=1; end M;",
      "model M Real x; equation der(x)=1; end N;",
      "model M Real x; equation der(x)=1; end M",
      "model M Real x,y; equation der(x)=1; end M;",
      "model M Real x; equation der(x)=1.0; end M;",
      "modelM Real x; equation der(x)=1; end modelM;",
      "model M Realx; equation der(x)=1; end M;",
      "model M Real x; equation der(x)=1; endM;",
      "model M Real x; equation der(x)=1; end M; /* unclosed",
      "model M Real 'x'; equation der('x')=1; end M;",
      "model M Real λ; equation der(λ)=1; end M;",
      "// comment\n" ++ good, "/* comment */" ++ good] do
    expect s!"reject {repr bad}" (!accepted bad)
  for keyword in reserved do
    expect s!"reserved identifier {keyword}" (!accepted
      s!"model M Real {keyword}; equation der({keyword})=1; end M;")
  for s in ["s = \"x\";", "s = [\"x\"], {\"y\" | \"z\"};",
      "s = other; other = (\"a\" | \"b\"), IDENT;", "s = \"\";",
      "(* comment *) s = { [ \"x\" ] }; "] do
    expect s!"EBNF accepts {repr s}" (grammarLowered s)
  for s in ["s : 'a' 'b';", "s : keyword IDENT; keyword : 'model';",
      "// reference-style grammar\ns : [ 'a' ] { 'b' | 'c' };", "s : ''; // end", "s : '(' s ')' | '';"] do
    expect s!"reference EBNF accepts {repr s}" (grammarLowered s)
  for s in ["", "s=missing;", "s=\"a\"; s=\"b\";",
      "s=\"a\"; unused=missing;",
      "IDENT=\"a\";", "s=[\"a\";", "s=\"a\"", "s=\"unclosed;"] do
    expect s!"EBNF rejects {repr s}" (!grammarLowered s)
  for s in ["s : 'unclosed;", "s : 'a'^;", "s : ident@name;", "s : /[a-z]+/;",
      "s : 'a',;", "s : : 'a';", "s : missing;"] do
    expect s!"unsupported reference EBNF rejects {repr s}" (!grammarLowered s)
  match compile (.single "rumoca-check:/compiler/Integrator.mo" good) with
  | .error e => throw (IO.userError s!"{e.phase}: {e.message}")
  | .ok a =>
    for x in ([0.0, 0.5, -1.5, 42.25] : List Float) do
      expect "target RHS" (C.eval x a.target.rhs == 1)
      expect "target step" (C.eval x a.target.step == x + 1)
    expect "binary64 tie rounds to even" (C.eval (9007199254740992.0 : Float) a.target.step == 9007199254740992.0)
    expect "10000 steps" (C.run a.target (7.5 : Float) 10000 == 10007.5)
  -- eFMI manifest identity generation. Native boundary: OS entropy, the
  -- SOURCE_DATE_EPOCH environment mode and the wall clock live outside the proof
  -- model, so the layout and mode selection are checked here directly.
  let efmiSource := "model Integrator Real x; equation der(x) = 1; end Integrator;"
  let hexDigit (uuid : String) (index : Nat) : Char :=
    (uuid.toList.filter (fun c => c != '{' && c != '}' && c != '-'))[index]!
  let isVariant (c : Char) : Bool := c == '8' || c == '9' || c == 'a' || c == 'b'
  for _ in [0, 1, 2] do
    let random ← EFMIIdentity.randomUUID
    expect "random eFMI identity is a version 4 UUID" (hexDigit random 12 == '4')
    expect "random eFMI identity carries the RFC 9562 variant" (isVariant (hexDigit random 16))
  let reproducible := EFMIIdentity.derivedIdentity "Integrator" efmiSource 0
  expect "reproducible eFMI identity is deterministic"
    (reproducible == EFMIIdentity.derivedIdentity "Integrator" efmiSource 0)
  expect "reproducible eFMI identity passes the manifest identity checker"
    (EFMI.Manifest.Identity.valid reproducible)
  for id in [reproducible.container, reproducible.algorithm, reproducible.production] do
    expect "reproducible eFMI identity is a version 5 UUID" (hexDigit id 12 == '5')
    expect "reproducible eFMI identity carries the RFC 9562 variant" (isVariant (hexDigit id 16))
  expect "reproducible eFMI identities are distinct"
    (decide (EFMI.Manifest.Identity.Distinct reproducible))
  expect "reproducible eFMI identity tracks the source text"
    (reproducible != EFMIIdentity.derivedIdentity "Integrator" (efmiSource ++ " ") 0)
  expect "SOURCE_DATE_EPOCH zero formats to the Unix epoch"
    (EFMIIdentity.epochGenerated 0 == "1970-01-01T00:00:00Z")
  expect "SOURCE_DATE_EPOCH formats a known instant"
    (EFMIIdentity.epochGenerated 1234567890 == "2009-02-13T23:31:30Z")
  IO.println "Lean regression tests passed"
