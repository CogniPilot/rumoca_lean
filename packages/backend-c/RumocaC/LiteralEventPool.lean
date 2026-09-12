import RumocaC.LiteralPoolLowering
import RumocaC.LiteralEventLowering
import RumocaC.LiteralEventInterface

/-! Compose the interface and syntax passes for a collected literal pool.
All observable behaviors agree, including faults and divergent event histories. -/
noncomputable section
namespace Rumoca.CLiteral
open CTree CMemory
variable {reserved : List String}

/-- Retain the program's external relations and symbolic function addresses
while constructing the named-object interface and lowering string syntax. -/
def Pool.eventProgram (pool : Pool reserved) (header : CInterface) (firstBlock : Nat)
    (original : @CCalls.Events.Program (pool.interface header firstBlock) E) :
    @CCalls.Events.Program (pool.namedInterface header firstBlock) E :=
  @Lowering.Events.program (pool.namedInterface header firstBlock) E pool.symbols
    (Interface.Events.program (before := pool.interface header firstBlock)
      (after := pool.namedInterface header firstBlock) rfl original)

theorem Pool.event_invocation_behaviors (pool : Pool reserved) (header : CInterface) (firstBlock : Nat)
    (fresh : pool.HeaderFresh header)
    (original : @CCalls.Events.Program (pool.interface header firstBlock) E)
    (covered : ProgramNamesCovered reserved
      (@CCalls.Events.Program.internal (pool.interface header firstBlock) E original))
    (calls : ∀ name fn,
      (@CCalls.Events.Program.internal (pool.interface header firstBlock) E original).definitions name =
        some (.tree fn) → ∀ stmt ∈ fn.body, Lowering.CallsWellFormed stmt)
    (name : String) (args : List Value) (heap : Heap)
    (behavior : Transition.Events.Observation E CBody.Result) :
    (@CCalls.Events.machine E (pool.namedInterface header firstBlock)
        (pool.eventProgram header firstBlock original)).Behaves (.calling name args heap .done) behavior ↔
      (@CCalls.Events.machine E (pool.interface header firstBlock) original).Behaves
        (.calling name args heap .done) behavior := by
  let extended := Interface.Events.program (before := pool.interface header firstBlock)
    (after := pool.namedInterface header firstBlock) rfl original
  exact (@Lowering.Events.invocation_behaviors (pool.namedInterface header firstBlock) pool.symbols E
    pool.noIntrinsic (pool.globalBindings header firstBlock fresh) extended
    (pool.program_safe header firstBlock covered calls) name args heap behavior).trans
      (Interface.Events.invocation_behaviors (pool.interface header firstBlock)
        (pool.namedInterface header firstBlock) rfl rfl original
        (pool.program_agrees header firstBlock covered) name args heap behavior)

end Rumoca.CLiteral
