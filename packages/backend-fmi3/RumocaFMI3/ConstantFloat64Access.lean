import RumocaFMI3.TensorFloat64Access
import RumocaFMI3.ConstantDerivative

/-! The constant-rate `fmi3GetFloat64` evaluation and its contract, as a
package-checked product.

The constant-rate adapter emits the table-driven Float64 accessors
(`TensorFloat64.getFunction`, `TensorFloat64.setFunction`) over its declared
interface: `0` the independent time base, then each scalar source state and its
derivative, each at its own element of the record's state and derivative
blocks. The state derivatives are calculated variables: before staging a
`der(...)` reference the getter evaluates the whole rate vector through the
constant kernel entry (`ConstantDerivative.entryCall`), as the derivative getter
does, so the returned value is the state's rate whatever the region held before.
There is no algebraic output. -/
noncomputable section
namespace Rumoca.FMI3.ConstantFloat64
open CTree CMemory CBody CLoops
open Rumoca.FMI3.TensorInstance
open Rumoca.CMemory.TensorView
open Rumoca.FMI3.TensorFloat64 (getLoopSuffix countReject)
open Rumoca.FMI3.Float64Table (getArm)
open CTree.Printer
open Rumoca.FMI3.Float64Calls (arguments parameters)

/-- The constant-rate evaluations: the rate vector for the derivatives, nothing for
outputs. -/
def reads : Float64Table.Reads := ⟨[ConstantDerivative.entryCall], []⟩

theorem reads_noDecl : (reads.derivative ++ reads.output).all CLoops.noDeclarations = true := by
  simp [reads, ConstantDerivative.entryCall, CLoops.noDeclarations]

theorem reads_printable :
    ∀ stmt ∈ reads.derivative ++ reads.output, ItemPrintable RuntimePrinter.typedefs stmt := by
  intro stmt member
  simp only [reads, List.append_nil, List.mem_singleton] at member
  subst member
  exact ConstantDerivative.entryCall_printable

/-! ### A state derivative is evaluated when it is read -/

section
variable [static : StaticLiterals]
private local instance readInterface : CInterface := cInterface static.addresses
variable (program : CCalls.Events.Program E)

/-- The value of one element of the rate vector, as a scalar variable. -/
def rateAt (rates : List Rumoca.ConstantProfile.Decimal) (shape : Tensor.Shape)
    (len : rates.length = shape.volume) (k : Fin shape.volume) : Values Tensor.scalar :=
  Tensor.Value.fill Tensor.scalar (ConstantInstanceRhs.ratesVec rates shape len)[k]

/-- Reading the derivative of the `k`-th state of instance `i`: the getter
evaluates the rate vector through the constant kernel entry, returns the `k`-th
exactly rounded rate with `fmi3OK`, leaves the rate vector in the derivative
block and preserves every other instance, whatever the block held before the
call. -/
theorem get_derivative_reaches (shape : Tensor.Shape) (iface : Solve.Interface) (reference : Nat)
    (k : Fin shape.volume)
    (arm : (Float64Table.getArms reads iface).lookup reference =
      some (ConstantDerivative.entryCall :: getArm ⟨derivativeName, k.val, 1⟩))
    (rates : List Rumoca.ConstantProfile.Decimal)
    (len : rates.length = shape.volume) (definitions : CLoops.Calls.Definitions)
    (linked : CCalls.Typed.Extends definitions program.internal)
    (found : definitions "rumoca_constant_rhs" = some (Rumoca.CConstant.rhsFunction rates))
    (ptrTy : (cInterface static.addresses).types "double *" = some .pointer)
    (backing : Heap) (pool : Address) (i : Nat) (time : Values Tensor.scalar) (state : Values shape)
    (refs buffer : Address) (n m : UInt64) (kind : Kind) (mode : Mode) (stack : CCalls.Typed.Continuation)
    (nref : n.toNat = 1) (nval : m.toNat = 1)
    (defined : program.internal.definitions "fmi3GetFloat64" = some (.tree (TensorFloat64.getFunction reads iface)))
    (hk : load (TensorInstance.constantStore backing pool i shape time state)
      ((TensorInstance.record pool i).member "kind") = some (.integer kind.code))
    (hm : load (TensorInstance.constantStore backing pool i shape time state)
      ((TensorInstance.record pool i).member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode)
    (refRead : load (TensorInstance.constantStore backing pool i shape time state)
      (refs.index 0) = some (.integer reference))
    (writable : Writable (TensorInstance.constantStore backing pool i shape time state) buffer 1)
    (separate : ∀ a < shape.volume, ∀ b < 1,
      (TensorInstance.field pool i derivativeName).index a ≠ buffer.index b)
    (resolves : ∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling "rumoca_constant_rhs" [.pointer (some (TensorInstance.field pool i derivativeName))]
        (TensorInstance.constantStore backing pool i shape time state) .done) v →
      CCalls.Events.Resolves program v) :
    ∃ finalHeap,
      Reads finalHeap (TensorInstance.field pool i derivativeName) (ConstantInstanceRhs.ratesVec rates shape len) ∧
      (∀ (j : Nat) (b : String) (l : Nat), j ≠ i →
        finalHeap ((TensorInstance.field pool j b).index l) =
          (TensorInstance.constantStore backing pool i shape time state) ((TensorInstance.field pool j b).index l)) ∧
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.calling "fmi3GetFloat64" (arguments (some (TensorInstance.record pool i)) (some refs) (some buffer) n m)
          (TensorInstance.constantStore backing pool i shape time state) stack)
        (.returning (.integer 0) (written finalHeap buffer (rateAt rates shape len k) 1) stack) := by
  let H := TensorInstance.constantStore backing pool i shape time state
  let p := TensorInstance.record pool i
  obtain ⟨types0, entered⟩ := TensorFloat64.guard_reaches reads iface reads_noDecl program H p refs buffer
    n m kind mode defined hk hm allowed nref stack
  have declared := TensorFloat64.declares_reaches program reads iface
    (TensorFloat64.guardEnv p refs buffer n m) types0 H stack
    (by simp [TensorFloat64.guardEnv, parameters, CBody.bind])
    (by simp [TensorFloat64.guardEnv, parameters, CBody.bind])
  let env := TensorFloat64.declaredEnv (TensorFloat64.guardEnv p refs buffer n m)
  let rest := countReject :: getLoopSuffix
  have nav := TensorFloat64.dispatch_reaches program env (TensorFloat64.declaredTypes types0) H refs reference
    "fmi3Status" stack
    (by simp [env, TensorFloat64.declaredEnv, TensorFloat64.guardEnv, parameters, CBody.bind, CBody.resolve])
    refRead (Runtime.fail "Unknown value reference") (TensorFloat64.fail_noDecl _) _
    (Float64Table.getArms_noDecl reads iface reads_noDecl) _ arm rest
  obtain ⟨finalHeap, reads', frame, others, ran⟩ := ConstantDerivative.entryCall_reaches program shape rates len
    definitions linked found ptrTy H pool i env (TensorFloat64.declaredTypes types0)
    (getArm ⟨derivativeName, k.val, 1⟩ ++ rest) "fmi3Status" stack
    (by simp [env, TensorFloat64.declaredEnv, TensorFloat64.guardEnv, CBody.bind, p])
    (by simp [env, TensorFloat64.declaredEnv, TensorFloat64.guardEnv, parameters, CBody.bind])
    (TensorInstance.constant_writable_derivative backing pool i shape time state) resolves
  have writableFinal : Writable finalHeap buffer 1 := by
    intro b hb
    obtain ⟨old, ho⟩ := writable b hb
    exact ⟨old, (frame (buffer.index b) (fun a ha => (separate a ha b hb).symm)).trans ho⟩
  have element : Reads finalHeap ((p.member derivativeName).index k.val) (rateAt rates shape len k) := by
    intro l
    have single : l.val = 0 := by
      have bound := l.isLt
      have one : Tensor.scalar.volume = 1 := rfl
      omega
    have cell := reads' k
    have value : (rateAt rates shape len k)[l] = (ConstantInstanceRhs.ratesVec rates shape len)[k] := by
      simp [rateAt]
    rw [value, show ((p.member derivativeName).index k.val).index l.val = (p.member derivativeName).index k.val by
      rw [single]; exact Address.index_zero _]
    exact cell
  have staged := TensorFloat64.stage_reaches program (TensorFloat64.guardEnv p refs buffer n m) types0 finalHeap p
    ⟨derivativeName, k.val, 1⟩ rest stack (show (1 : Nat) < 2 ^ 64 by decide)
    (by simp [TensorFloat64.guardEnv, CBody.bind])
    (fun h => absurd h (show derivativeName ≠ timeName by decide))
  have tail := TensorFloat64.get_tail_reaches program (TensorFloat64.guardEnv p refs buffer n m)
    (TensorFloat64.declaredTypes types0) finalHeap ((p.member derivativeName).index k.val) buffer Tensor.scalar
    (rateAt rates shape len k) m stack (by decide) nval
    (by simp [TensorFloat64.stagedEnv, TensorFloat64.regionBase, CBody.bind, CBody.resolve])
    (by simp [TensorFloat64.stagedEnv, CBody.bind, CBody.resolve, Tensor.scalar, Tensor.Shape.volume])
    (by simp [TensorFloat64.stagedEnv, TensorFloat64.declaredEnv, TensorFloat64.guardEnv, parameters, CBody.bind,
      CBody.resolve])
    (by simp [TensorFloat64.stagedEnv, TensorFloat64.declaredEnv, TensorFloat64.guardEnv, parameters, CBody.bind,
      CBody.resolve])
    (by simp [TensorFloat64.stagedEnv, TensorFloat64.declaredEnv, TensorFloat64.guardEnv, parameters, CBody.bind])
    (by simp [TensorFloat64.stagedEnv, TensorFloat64.declaredEnv, TensorFloat64.guardEnv, parameters, CBody.bind])
    element writableFinal (fun a ha b hb => by
      have a0 : a = 0 := by simp [Tensor.scalar, Tensor.Shape.volume] at ha; omega
      subst a0
      simpa [Address.index] using separate k.val k.isLt b (by simpa [Tensor.scalar, Tensor.Shape.volume] using hb))
  have stagedEq : TensorFloat64.stagedEnv (TensorFloat64.guardEnv p refs buffer n m)
      (TensorFloat64.regionBase p ⟨derivativeName, k.val, 1⟩) 1 =
      TensorFloat64.stagedEnv (TensorFloat64.guardEnv p refs buffer n m)
        ((p.member derivativeName).index k.val) Tensor.scalar.volume := rfl
  rw [stagedEq] at staged
  refine ⟨finalHeap, reads', others, entered.trans (declared.trans (nav.trans ?_))⟩
  exact ran.trans (staged.trans tail)

end

/-! ### Consumable function contract -/

section
open CTree.Printer
variable [static : StaticLiterals]
private local instance contractInterface : CInterface := cInterface static.addresses

/-- The constant-rate `fmi3GetFloat64` function contract over the constant state
block of extent `shape.volume`. -/
structure GetContract (shape : Tensor.Shape) (iface : Solve.Interface) (text : String) : Prop where
  printed : text = (TensorFloat64.getFunction reads iface).render
  /-- Reading a state derivative evaluates the exactly rounded rate vector through
  the constant kernel entry and returns that state's rate; the block's earlier
  contents do not matter. -/
  derivativeRead : ∀ {E} (program : CCalls.Events.Program E) (reference : Nat) (k : Fin shape.volume)
    (rates : List Rumoca.ConstantProfile.Decimal)
    (len : rates.length = shape.volume) (definitions : CLoops.Calls.Definitions)
    (backing : Heap) (pool : Address) (i : Nat) (time : Values Tensor.scalar) (state : Values shape)
    (refs buffer : Address) (n m : UInt64) (kind : Kind) (mode : Mode),
    (Float64Table.getArms reads iface).lookup reference =
      some (ConstantDerivative.entryCall :: getArm ⟨derivativeName, k.val, 1⟩) →
    CCalls.Typed.Extends definitions program.internal →
    definitions "rumoca_constant_rhs" = some (Rumoca.CConstant.rhsFunction rates) →
    (cInterface static.addresses).types "double *" = some .pointer →
    n.toNat = 1 → m.toNat = 1 →
    program.internal.definitions "fmi3GetFloat64" = some (.tree (TensorFloat64.getFunction reads iface)) →
    load (TensorInstance.constantStore backing pool i shape time state)
      ((TensorInstance.record pool i).member "kind") = some (.integer kind.code) →
    load (TensorInstance.constantStore backing pool i shape time state)
      ((TensorInstance.record pool i).member "mode") = some (.integer mode.code) →
    Reference.Allowed .get kind mode →
    load (TensorInstance.constantStore backing pool i shape time state) (refs.index 0) = some (.integer reference) →
    Writable (TensorInstance.constantStore backing pool i shape time state) buffer 1 →
    (∀ a < shape.volume, ∀ b < 1, (TensorInstance.field pool i derivativeName).index a ≠ buffer.index b) →
    (∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling "rumoca_constant_rhs" [.pointer (some (TensorInstance.field pool i derivativeName))]
        (TensorInstance.constantStore backing pool i shape time state) .done) v →
      CCalls.Events.Resolves program v) →
    ∃ finalHeap,
      Reads finalHeap (TensorInstance.field pool i derivativeName) (ConstantInstanceRhs.ratesVec rates shape len) ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3GetFloat64" (arguments (some (TensorInstance.record pool i)) (some refs) (some buffer) n m)
          (TensorInstance.constantStore backing pool i shape time state) .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, written finalHeap buffer (rateAt rates shape len k) 1⟩
  closed : (TensorFloat64.getFunction reads iface).body.all CBodyEmbedding.closedBlocks = true
  denotes : FunctionDenotes RuntimePrinter.typedefs text (TensorFloat64.getFunction reads iface)
  rejected : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap) (refs buffer : Option Address)
    (n m : UInt64),
    program.internal.definitions "fmi3GetFloat64" = some (.tree (TensorFloat64.getFunction reads iface)) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetFloat64" (arguments none refs buffer n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩

theorem get_contract (shape : Tensor.Shape) (iface : Solve.Interface) :
    GetContract shape iface (TensorFloat64.getFunction reads iface).render where
  printed := rfl
  derivativeRead program reference k rates len definitions backing pool i time state refs buffer n m kind mode
      arm linked found ptrTy nref nval defined hk hm allowed refRead writable separate resolves := by
    obtain ⟨finalHeap, reads', _others, ran⟩ := get_derivative_reaches program shape iface reference k arm rates
      len definitions linked found ptrTy backing pool i time state refs buffer n m kind mode .done nref nval
      defined hk hm allowed refRead writable separate resolves
    exact ⟨finalHeap, reads', fun behavior =>
      (CCalls.Events.internal_prefix program ran (CCalls.Events.return_forced program _ _)).behaviors behavior⟩
  closed := TensorFloat64.getBody_closed reads iface reads_noDecl
  denotes := TensorFloat64.getFunction_denotes reads iface reads_printable
  rejected program heap refs buffer n m defined :=
    TensorFloat64.null_get_behaviors reads iface reads_noDecl program heap refs buffer n m defined

end

end Rumoca.FMI3.ConstantFloat64
