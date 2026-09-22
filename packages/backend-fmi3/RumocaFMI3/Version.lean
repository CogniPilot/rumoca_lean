import RumocaFMI3.BodyEmbedding
import RumocaFMI3.RuntimePrinter
import RumocaC.LiteralPointers
import RumocaFMI3.LiteralPreparation

/-! Complete version calls on the actual rendered definition table. Literal
objects are constructed from its collected pool; no instance or lifecycle state
is required. Native headers, allocation and ABI correspondence remain separate. -/
noncomputable section
namespace Rumoca.FMI3.Version
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses
open CTree CMemory

def signature : Signature := ⟨"const char *", "fmi3GetVersion", []⟩

theorem call_reaches (model : Solve.FMI3Model source) (program : CCalls.Program)
    (heap : Heap) (base : Address) (stack : CCalls.Typed.Continuation)
    (defined : program.definitions signature.name = some (.tree (Runtime.function model signature)))
    (bound : static.addresses "3.0" = some base) :
    Transition.Reaches (CCalls.Typed.machine program).step
      (.calling signature.name [] heap stack) (.returning (.pointer (some base)) heap stack) := by
  apply CBodyEmbedding.typed_call_reaches program (Runtime.function model signature)
    [] (fun _ => none) heap ⟨.pointer (some base), heap⟩ (.pointer (some base)) stack 1
    defined rfl (BodyEmbedding.body_closed model signature) ?_ ?_
  · simp [CBody.run, CBody.next, CBody.nextWith, CBody.legacyExpressions, Runtime.function, Runtime.body, signature,
      Runtime.ret, CBody.eval, CBody.evalWith, bound]
  · simp [Runtime.function, signature, CCalls.returnCast, CBody.cast, convert]

theorem call_behaviors (model : Solve.FMI3Model source) (program : CCalls.Program)
    (heap : Heap) (base : Address)
    (defined : program.definitions signature.name = some (.tree (Runtime.function model signature)))
    (bound : static.addresses "3.0" = some base) (behavior) :
    (CCalls.Typed.machine program).Behaves
      (.calling signature.name [] heap .done) behavior ↔
      behavior = .terminates ⟨.pointer (some base), heap⟩ :=
  (CCalls.Typed.machine program).behavior_iff
    ((call_reaches model program heap base .done defined bound).trans (.next rfl (.refl _))) rfl

theorem returned_bytes (model : Solve.FMI3Model source) (program : CCalls.Program)
    (heap : Heap) (base : Address) (signed : Bool)
    (defined : program.definitions signature.name = some (.tree (Runtime.function model signature)))
    (bound : static.addresses "3.0" = some base)
    (stored : CLiteral.Stored signed heap base "3.0") :
    (∀ behavior, (CCalls.Typed.machine program).Behaves
      (.calling signature.name [] heap .done) behavior ↔
      behavior = .terminates ⟨.pointer (some base), heap⟩) ∧
    (∀ index byte, (CLiteral.bytes "3.0")[index]? = some byte →
      CLiteral.readByte heap (base.index index) = some byte) :=
  ⟨call_behaviors model program heap base defined bound,
    fun _ _ member => stored.read_byte member⟩

omit static in
theorem collected (model : Solve.FMI3Model source) :
    "3.0" ∈ CLiteral.functionTexts (Runtime.function model signature) := by
  simp [Runtime.function, Runtime.body, signature, Runtime.ret,
    CLiteral.functionTexts, CLiteral.statementTexts, CLiteral.expressionTexts]

omit static in
theorem literal_bound (model : Solve.FMI3Model source) (signatures : List Signature)
    {pool : CLiteral.Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model signatures).flatMap CLiteral.functionNames)}
    (made : LiteralPreparation.prepare model signatures = some pool)
    (member : signature ∈ signatures) (firstBlock : Nat) :
    ∃ base, pool.addresses firstBlock "3.0" = some base :=
  LiteralPreparation.message_bound model signatures made signature member "3.0" (collected model) firstBlock

def PreparedContract (model : Solve.FMI3Model source) (signatures : List Signature)
    (pool : CLiteral.Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model signatures).flatMap CLiteral.functionNames)) : Prop :=
  ∀ (before : Heap) (firstBlock : Nat) (signed : Bool),
    ∃ base, pool.addresses firstBlock "3.0" = some base ∧
      (∀ behavior, (@CCalls.Typed.machine (cInterface (pool.addresses firstBlock))
        (LiteralPreparation.program model signatures)).Behaves
        (.calling signature.name [] (pool.install before firstBlock signed) .done) behavior ↔
        behavior = .terminates ⟨.pointer (some base), pool.install before firstBlock signed⟩) ∧
      CLiteral.Stored signed (pool.install before firstBlock signed) base "3.0" ∧
      (∀ index byte, (CLiteral.bytes "3.0")[index]? = some byte →
        CLiteral.readByte (pool.install before firstBlock signed) (base.index index) = some byte)

omit static in
theorem prepared_correct (model : Solve.FMI3Model source) (signatures : List Signature)
    {pool : CLiteral.Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model signatures).flatMap CLiteral.functionNames)}
    (made : LiteralPreparation.prepare model signatures = some pool)
    (unique : ((LiteralPreparation.functions model signatures).map (fun fn => fn.signature.name)).Nodup)
    (member : signature ∈ signatures) : PreparedContract model signatures pool := by
  intro before firstBlock signed
  obtain ⟨base, bound⟩ := literal_bound model signatures made member firstBlock
  have defined := LiteralPreparation.function_bound model signatures unique signature member
  have result := returned_bytes (static := ⟨pool.addresses firstBlock⟩) model
    (LiteralPreparation.program model signatures) (pool.install before firstBlock signed)
    base signed defined bound (pool.storage_valid before firstBlock signed _ _ bound)
  exact ⟨base, bound, result.1, pool.storage_valid before firstBlock signed _ _ bound, result.2⟩

omit static in
theorem function_tokenization (model : Solve.FMI3Model source) :
    CTree.Printer.FunctionTokenization RuntimePrinter.typedefs
      (Runtime.function model signature).render (Runtime.function model signature) := by
  apply RuntimePrinter.function_tokenization
  refine ⟨CTree.Syntax.TypeSpelling.pointer
    (CTree.Syntax.TypeSpelling.const (CTree.Syntax.TypeSpelling.named (.primitive (name := "char") (by decide +kernel)))),
    by decide +kernel, ?_⟩
  intro param member
  simp [signature] at member

structure FunctionContract (model : Solve.FMI3Model source) (sigs : List Signature) (text : String) : Prop where
  member : signature ∈ sigs
  printed : text = (Runtime.function model signature).render
  tokenization : CTree.Printer.FunctionTokenization RuntimePrinter.typedefs text
    (Runtime.function model signature)
  prepared : ∀ pool, LiteralPreparation.prepare model sigs = some pool →
    PreparedContract model sigs pool

omit static in
theorem rendered_contract (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature ∈ sigs) :
    FunctionContract model sigs (Runtime.function model signature).render := by
  refine ⟨member, rfl, function_tokenization model, ?_⟩
  intro pool made
  exact prepared_correct model sigs made unique member

end Rumoca.FMI3.Version
