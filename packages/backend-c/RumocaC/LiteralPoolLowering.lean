import RumocaC.LiteralPoolStorage

/-! Derive the literal-lowering invariants from collected source identifiers
and a checked pool. Header name exclusion and the definition-table connection
remain explicit; emitted declarations and native linkage are separate. -/
namespace Rumoca.CLiteral
open CTree CMemory
variable {reserved : List String}

def statementNames : Stmt → List String
  | .declare _ name value => name :: Interface.names value
  | .assign target value => Interface.names target ++ Interface.names value
  | .eval value | .ret (some value) => Interface.names value
  | .ret none => []
  | .branch condition yes no => Interface.names condition ++
      yes.flatMap statementNames ++ no.flatMap statementNames
  | .whileLoop condition body => Interface.names condition ++ body.flatMap statementNames

def functionNames (fn : Function) : List String :=
  fn.signature.name :: (fn.signature.parameters.map Parameter.name ++ fn.body.flatMap statementNames)

theorem Pool.freshName (pool : Pool reserved) (member : name ∈ reserved) :
    Lowering.FreshName pool.symbols name := by
  intro text named
  simp only [Pool.symbols, Option.map_eq_some_iff] at named
  obtain ⟨entry, found, rfl⟩ := named
  exact (pool.entry_fresh (lookup_mem found)).2 member

/-- Collect reads as well as declarations and writes: adding a new global
must not turn a previously missing identifier into a successful lookup. -/
theorem Pool.statement_safe (pool : Pool reserved) (header : CInterface) (firstBlock : Nat)
    (stmt : Stmt) (covered : ∀ name ∈ statementNames stmt, name ∈ reserved) :
    Interface.StmtAgrees (pool.interface header firstBlock) (pool.namedInterface header firstBlock) stmt ∧
      Lowering.FreshWrites pool.symbols stmt := by
  revert covered
  induction stmt using Stmt.rec (motive_2 := fun code => ∀ stmt ∈ code,
      (∀ name ∈ statementNames stmt, name ∈ reserved) →
        Interface.StmtAgrees (pool.interface header firstBlock) (pool.namedInterface header firstBlock) stmt ∧
          Lowering.FreshWrites pool.symbols stmt) with
  | declare type name value =>
      intro covered
      simp only [Interface.StmtAgrees, Lowering.FreshWrites]
      exact ⟨fun used member => pool.reserved_agreement header firstBlock
        (covered used (by simp [statementNames, member])),
        pool.freshName (covered name (by simp [statementNames]))⟩
  | assign target value =>
      intro covered
      refine ⟨?_, ?_⟩
      · simp only [Interface.StmtAgrees]
        exact ⟨fun used member => pool.reserved_agreement header firstBlock
          (covered used (by simp [statementNames, member])),
          fun used member => pool.reserved_agreement header firstBlock
            (covered used (by simp [statementNames, member]))⟩
      · cases target <;> simp only [Lowering.FreshWrites]
        exact pool.freshName (covered _ (by simp [statementNames, Interface.names]))
  | eval value =>
      intro covered
      simp only [Interface.StmtAgrees, Lowering.FreshWrites]
      exact ⟨fun used member => pool.reserved_agreement header firstBlock
        (covered used (by simpa only [statementNames] using member)), trivial⟩
  | ret value =>
      intro covered
      cases value with
      | none => simp [Interface.StmtAgrees, Lowering.FreshWrites]
      | some value =>
          simp only [Interface.StmtAgrees, Lowering.FreshWrites]
          exact ⟨fun used member => pool.reserved_agreement header firstBlock
            (covered used (by simpa only [statementNames] using member)), trivial⟩
  | branch condition yes no hy hn =>
      intro covered
      have yesSafe : ∀ stmt ∈ yes,
          Interface.StmtAgrees (pool.interface header firstBlock) (pool.namedInterface header firstBlock) stmt ∧
            Lowering.FreshWrites pool.symbols stmt := by
        intro stmt member
        apply hy stmt member
        intro name used
        apply covered name
        simp only [statementNames, List.mem_append]
        exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨stmt, member, used⟩))
      have noSafe : ∀ stmt ∈ no,
          Interface.StmtAgrees (pool.interface header firstBlock) (pool.namedInterface header firstBlock) stmt ∧
            Lowering.FreshWrites pool.symbols stmt := by
        intro stmt member
        apply hn stmt member
        intro name used
        apply covered name
        simp only [statementNames, List.mem_append]
        exact Or.inr (List.mem_flatMap.mpr ⟨stmt, member, used⟩)
      simp only [Interface.StmtAgrees, Lowering.FreshWrites]
      exact ⟨⟨fun used member => pool.reserved_agreement header firstBlock
        (covered used (by simp [statementNames, member])),
        fun stmt member => (yesSafe stmt member).1, fun stmt member => (noSafe stmt member).1⟩,
        fun stmt member => (yesSafe stmt member).2, fun stmt member => (noSafe stmt member).2⟩
  | whileLoop condition body hb =>
      intro covered
      have bodySafe : ∀ stmt ∈ body,
          Interface.StmtAgrees (pool.interface header firstBlock) (pool.namedInterface header firstBlock) stmt ∧
            Lowering.FreshWrites pool.symbols stmt := by
        intro stmt member
        apply hb stmt member
        intro name used
        apply covered name
        simp only [statementNames, List.mem_append]
        exact Or.inr (List.mem_flatMap.mpr ⟨stmt, member, used⟩)
      simp only [Interface.StmtAgrees, Lowering.FreshWrites]
      exact ⟨⟨fun used member => pool.reserved_agreement header firstBlock
        (covered used (by simp [statementNames, member])),
        fun stmt member => (bodySafe stmt member).1⟩, fun stmt member => (bodySafe stmt member).2⟩
  | nil => simp_all
  | cons stmt rest hs hr =>
      rename_i value member covered
      rcases List.mem_cons.mp member with rfl | member
      · exact hs covered
      · exact hr value member covered

def ProgramNamesCovered (reserved : List String) (program : CCalls.Program) : Prop :=
  ∀ name fn, program.definitions name = some (.tree fn) →
    ∀ used ∈ functionNames fn, used ∈ reserved

theorem collected_names_cover (functions : List Function) (program : CCalls.Program)
    (defined : ∀ name fn, program.definitions name = some (.tree fn) → fn ∈ functions) :
    ProgramNamesCovered (extra ++ functions.flatMap functionNames) program := by
  intro name fn found used member
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨fn, defined name fn found, member⟩)

theorem Pool.program_agrees (pool : Pool reserved) (header : CInterface) (firstBlock : Nat)
    (covered : ProgramNamesCovered reserved program) :
    Interface.ProgramAgrees (pool.interface header firstBlock) (pool.namedInterface header firstBlock) program := by
  intro name fn found stmt member
  apply (pool.statement_safe header firstBlock stmt ?_).1
  intro used inStmt
  apply covered name fn found used
  simp only [functionNames, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inr (List.mem_flatMap.mpr ⟨stmt, member, inStmt⟩))

theorem Pool.program_safe (pool : Pool reserved) (header : CInterface) (firstBlock : Nat)
    (covered : ProgramNamesCovered reserved program)
    (calls : ∀ name fn, program.definitions name = some (.tree fn) →
      ∀ stmt ∈ fn.body, Lowering.CallsWellFormed stmt) : Lowering.ProgramSafe pool.symbols program := by
  intro name fn found
  refine ⟨?_, ?_, calls name fn found⟩
  · intro parameter member
    apply pool.freshName
    apply covered name fn found parameter.name
    simp only [functionNames, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inl (List.mem_map.mpr ⟨parameter, member, rfl⟩))
  · intro stmt member
    apply (pool.statement_safe header firstBlock stmt ?_).2
    intro used inStmt
    apply covered name fn found used
    simp only [functionNames, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inr (List.mem_flatMap.mpr ⟨stmt, member, inStmt⟩))

noncomputable section
/-- Compose global dictionary extension with literal lowering. This relates
the original interface to the lowered program's named interface and preserves
all return/heap, failure and divergence observations. -/
theorem Pool.invocation_behaviors (pool : Pool reserved) (header : CInterface) (firstBlock : Nat)
    (fresh : pool.HeaderFresh header) (program : CCalls.Program)
    (covered : ProgramNamesCovered reserved program)
    (calls : ∀ name fn, program.definitions name = some (.tree fn) →
      ∀ stmt ∈ fn.body, Lowering.CallsWellFormed stmt)
    (name : String) (args : List Value) (heap : Heap) (behavior : Transition.Observation CBody.Result) :
    (@CCalls.Typed.machine (pool.namedInterface header firstBlock) (Lowering.program pool.symbols program)).Behaves
      (.calling name args heap .done) behavior ↔
    (@CCalls.Typed.machine (pool.interface header firstBlock) program).Behaves
      (.calling name args heap .done) behavior := by
  exact (@Lowering.invocation_behaviors (pool.namedInterface header firstBlock) pool.symbols
    pool.noIntrinsic (pool.globalBindings header firstBlock fresh) program
    (pool.program_safe header firstBlock covered calls)
    name args heap behavior).trans
      (Interface.invocation_behaviors (pool.interface header firstBlock) (pool.namedInterface header firstBlock)
        rfl rfl program (pool.program_agrees header firstBlock covered) name args heap behavior)

end
end Rumoca.CLiteral
