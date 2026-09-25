import RumocaC.FeatureInventory
import RumocaC.PrinterCertificate
import Lean

/-! Kernel certificate of the feature inventory of actual file bytes.

The input is the character list an artifact checker has already bound to an
actual file (`quoteCharacters`, blocks of `characterBlockSize` characters chained
through `part_i` definitions). The metaprogram only proposes the scanner state
after each block; the kernel checks every block transition by evaluation, the
composed inventory equality, and the two decidable predicates. Native scanning
has no proof authority. -/
namespace Rumoca.CFeatures.Certificate
open Lean Elab Command Meta

deriving instance ToExpr for Inventory
deriving instance ToExpr for Mode
deriving instance ToExpr for State

private def addChecked (name : Name) (type proof : Expr) : MetaM Unit := do
  let type ← instantiateMVars type
  let proof ← instantiateMVars proof
  addDecl (.thmDecl { name, levelParams := [], type, value := proof })

/-- The block list and the rest of a quoted-character part `[block] ++ next`. -/
private def blockOf (part : Name) : MetaM (Expr × Expr) := do
  let info ← getConstInfo part
  let some value := info.value? | throwError "quoted character part {part} has no definition"
  let args := value.getAppArgs
  unless value.isAppOfArity ``HAppend.hAppend 6 do
    throwError "quoted character part {part} is not a block followed by the next part"
  return (args[4]!, args[5]!)

/-- Certify `inventory chars = inv`, `allocationFree inv` and `featureFree inv`
for the quoted characters named `quoted` (its `part_0` identifier `chars`), whose
native text is `input`. Emits `quoted.inventory_eq`, `quoted.allocation_free` and
`quoted.feature_free`; returns the inventory. -/
def certify (quoted : Name) (chars : Ident) (input : String) : CommandElabM Inventory := do
  let text := input.toList.toArray
  let count := (text.size + Rumoca.CTree.Printer.Certificate.characterBlockSize - 1) / Rumoca.CTree.Printer.Certificate.characterBlockSize
  let mut states : Array State := #[initial]
  for i in [:count] do
    let block := (text.toSubarray (i * Rumoca.CTree.Printer.Certificate.characterBlockSize)
      (min ((i + 1) * Rumoca.CTree.Printer.Certificate.characterBlockSize) text.size)).toArray.toList
    states := states.push (block.foldl step states[i]!)
  let final := states[count]!
  let result := finish final
  let part := fun i => quoted.str s!"part_{i}"
  unless chars.getId == part 0 do throwError "feature certificate expects the first quoted part"
  -- Walk back from the empty last part: `part_i.foldl step s_i = s_n`.
  let mut previous := quoted.str s!"inventory_part_{count}"
  liftTermElabM do
    let partN := mkConst (part count)
    let sN := toExpr final
    let lhs ← mkAppM ``List.foldl #[mkConst ``step, sN, partN]
    addChecked previous (← mkEq lhs sN) (← mkEqRefl sN)
  for j in [:count] do
    let i := count - 1 - j
    let current := quoted.str s!"inventory_part_{i}"
    let blockName := quoted.str s!"inventory_block_{i}"
    let next := previous
    liftTermElabM do
      let (block, rest) ← blockOf (part i)
      let si := if i = 0 then mkConst ``initial else toExpr states[i]!
      let sNext := toExpr states[i + 1]!
      let blockLhs ← mkAppM ``List.foldl #[mkConst ``step, si, block]
      addChecked blockName (← mkEq blockLhs sNext) (← mkEqRefl sNext)
      let joined ← mkAppM ``foldl_block #[block, rest, si, sNext, mkConst blockName]
      let lhs ← mkAppM ``List.foldl #[mkConst ``step, si, mkConst (part i)]
      let proof ← mkEqTrans joined (mkConst next)
      addChecked current (← mkEq lhs (toExpr final)) proof
    previous := current
  let inventoryEq := mkIdent (quoted.str "inventory_eq")
  liftTermElabM do
    let lhs ← mkAppM ``inventory #[mkConst (part 0)]
    let resultExpr := toExpr result
    let viaFinish ← mkCongrArg (mkConst ``finish) (mkConst previous)
    addChecked inventoryEq.getId (← mkEq lhs resultExpr) (← mkEqTrans viaFinish (← mkEqRefl resultExpr))
  let allocation := mkIdent (quoted.str "allocation_free")
  let feature := mkIdent (quoted.str "feature_free")
  elabCommand (← `(command| theorem $allocation:ident : allocationFree (inventory $chars) = true := by
    rw [$inventoryEq:ident]; decide +kernel))
  elabCommand (← `(command| theorem $feature:ident : featureFree (inventory $chars) = true := by
    rw [$inventoryEq:ident]; decide +kernel))
  for declaration in [inventoryEq.getId, allocation.getId, feature.getId] do
    let collected ← collectAxioms declaration
    for dependency in collected do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "invalid feature inventory certificate {declaration}: {dependency}"
  return result

end Rumoca.CFeatures.Certificate
