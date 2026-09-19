import RumocaC.LiteralPoolLowering

/-! Collect every string expression before constructing its named storage.
The removal theorem covers all expression and statement constructors; the
checked constructor retains partial failure for name collisions and bounds. -/
namespace Rumoca.CLiteral
open CTree CMemory
variable {reserved : List String}

def expressionTexts : Expr → List String
  | .str text => [text]
  | .bin _ a b | .index a b => expressionTexts a ++ expressionTexts b
  | .not a | .deref a | .address a | .field a _ _ | .cast _ a => expressionTexts a
  | .call fn args => expressionTexts fn ++ args.flatMap expressionTexts
  | .id _ | .nat _ | .decimal _ _ _ | .sizeof _ => []

def statementTexts : Stmt → List String
  | .declare _ _ value | .eval value | .ret (some value) => expressionTexts value
  | .assign target value => expressionTexts target ++ expressionTexts value
  | .ret none => []
  | .branch condition yes no => expressionTexts condition ++
      yes.flatMap statementTexts ++ no.flatMap statementTexts
  | .whileLoop condition body => expressionTexts condition ++ body.flatMap statementTexts

def functionTexts (fn : Function) : List String := fn.body.flatMap statementTexts

/-- The unregistered literals, in occurrence order, are exactly those retained
by lowering. Literal collection includes callees and nested call arguments. -/
theorem expressionTexts_lowered (symbols : Lowering.Symbols) (expr : Expr) :
    expressionTexts (Lowering.expression symbols expr) =
      (expressionTexts expr).filter (fun text => (symbols text).isNone) := by
  induction expr using Expr.rec (motive_2 := fun args =>
      (args.map (Lowering.expression symbols)).flatMap expressionTexts =
        (args.flatMap expressionTexts).filter (fun text => (symbols text).isNone)) with
  | str text => cases found : symbols text <;> simp [Lowering.expression, expressionTexts, found]
  | id name | nat name | sizeof name => simp [Lowering.expression, expressionTexts]
  | decimal negative mantissa exponent => simp [Lowering.expression, expressionTexts]
  | bin op a b ha hb | index a b ha hb =>
      simp [Lowering.expression, expressionTexts, ha, hb, List.filter_append]
  | not a ha | deref a ha | address a ha | cast _ a ha | field a _ _ ha =>
      simpa only [Lowering.expression, expressionTexts] using ha
  | call fn args hf ha =>
      simp only [Lowering.expression, expressionTexts, hf, ha, List.filter_append]
  | nil => rfl
  | cons expr args he ha => simp [he, ha, List.filter_append]

theorem statementTexts_lowered (symbols : Lowering.Symbols) (stmt : Stmt) :
    statementTexts (Lowering.statement symbols stmt) =
      (statementTexts stmt).filter (fun text => (symbols text).isNone) := by
  induction stmt using Stmt.rec (motive_2 := fun code =>
      (code.map (Lowering.statement symbols)).flatMap statementTexts =
        (code.flatMap statementTexts).filter (fun text => (symbols text).isNone)) with
  | declare type name value | eval value =>
      simp [Lowering.statement, statementTexts, expressionTexts_lowered]
  | assign target value =>
      simp [Lowering.statement, statementTexts, expressionTexts_lowered, List.filter_append]
  | ret value => cases value <;> simp [Lowering.statement, statementTexts, expressionTexts_lowered]
  | branch condition yes no hy hn =>
      simp [Lowering.statement, statementTexts, expressionTexts_lowered, hy, hn, List.filter_append]
  | whileLoop condition body hb =>
      simp [Lowering.statement, statementTexts, expressionTexts_lowered, hb, List.filter_append]
  | nil => rfl
  | cons stmt code hs hc => simp [hs, hc, List.filter_append]

theorem functionTexts_lowered (symbols : Lowering.Symbols) (fn : Function) :
    functionTexts (Lowering.function symbols fn) =
      (functionTexts fn).filter (fun text => (symbols text).isNone) := by
  simp only [functionTexts, Lowering.function, List.flatMap_map]
  induction fn.body with
  | nil => rfl
  | cons stmt code ih =>
      simp only [List.flatMap_cons, statementTexts_lowered, List.filter_append] at ih ⊢
      rw [ih]

def Pool.forFunctions (extra : List String) (functions : List Function) :
    Option (Pool (extra ++ functions.flatMap functionNames)) :=
  Pool.make (extra ++ functions.flatMap functionNames) (functions.flatMap functionTexts)

theorem Pool.forFunctions_coverage
    (made : Pool.forFunctions extra functions = some pool) :
    (∃ name, pool.symbols text = some name) ↔
      ∃ fn ∈ functions, text ∈ functionTexts fn := by
  simpa only [List.mem_flatMap] using Pool.make_coverage made

theorem Pool.forFunctions_complete
    (made : Pool.forFunctions extra functions = some pool) (member : fn ∈ functions) :
    functionTexts (Lowering.function pool.symbols fn) = [] := by
  rw [functionTexts_lowered]
  apply List.filter_eq_nil_iff.mpr
  intro text occurs
  obtain ⟨name, found⟩ := (Pool.forFunctions_coverage made).mpr ⟨fn, member, occurs⟩
  simp [found]

noncomputable section
/-- The same function list determines reserved identifiers and literal
coverage. Only its connection to the program table, header exclusions and
structurally supported calls remain supplied by the enclosing adapter. -/
theorem Pool.forFunctions_behaviors
    (made : Pool.forFunctions extra functions = some pool)
    (header : CInterface) (firstBlock : Nat) (fresh : pool.HeaderFresh header)
    (program : CCalls.Program)
    (defined : ∀ name fn, program.definitions name = some (.tree fn) → fn ∈ functions)
    (calls : ∀ fn ∈ functions, ∀ stmt ∈ fn.body, Lowering.CallsWellFormed stmt)
    (name : String) (args : List Value) (heap : Heap) (behavior : Transition.Observation CBody.Result) :
    (∀ fn ∈ functions, functionTexts (Lowering.function pool.symbols fn) = []) ∧
    ((@CCalls.Typed.machine (pool.namedInterface header firstBlock) (Lowering.program pool.symbols program)).Behaves
      (.calling name args heap .done) behavior ↔
    (@CCalls.Typed.machine (pool.interface header firstBlock) program).Behaves
      (.calling name args heap .done) behavior) :=
  ⟨fun _ member => pool.forFunctions_complete made member,
    pool.invocation_behaviors header firstBlock fresh program
      (collected_names_cover functions program defined)
      (fun name fn found => calls fn (defined name fn found)) name args heap behavior⟩

end
end Rumoca.CLiteral
